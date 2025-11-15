#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"
#include <stdlib.h>
#include <assert.h>

/**
 * @brief Creates the variable "x_{node,pos,stack_height}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param node A node.
 * @param pos The path position.
 * @param stack_height The highest cell occupied of the stack at that position.
 * @return Z3_ast
 */
Z3_ast tn_path_variable(Z3_context ctx, int node, int pos, int stack_height)
{
    char name[60];
    snprintf(name, 60, "node %d,pos %d, height %d", node, pos, stack_height);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,4}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_4_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "4 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}




/**
 * @brief Creates the variable "y_{pos,height,6}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_6_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "6 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Wrapper to have the correct size of the array representing the stack (correct cells of the stack will be from 0 to (get_stack_size(length)-1)).
 *
 * @param length The length of the sought path.
 * @return int
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}



/**
 * @brief on verifie s'il existe une arête entre (u,v)
 */
static int tn_has_edge_wrapper(const TunnelNetwork network, int u, int v)
{
    return tn_is_edge(network, u, v) ? 1 : 0;
}


/**
 * @brief---------------------------------------------------------------------------------------------------------
*------------------------------------------------------------------------------------------------------------
*-------------les debut d'implementation des conditions de reduction des tunnels vers SAT :------------------
*------------- Organisation : chaque famille de contraintes a sa propre fonction :---------------------------
*------------- tn_condition_initial_and_final : conditions terminales et initiales (pile vide).--------------
*------------- tn_condition_uniqueness : exactement une paire (node,height) vraie par position.--------------
*------------- tn_condition_edges : contraintes de voisinage (suivant doit être voisin dans le graphe).------
*------------- tn_condition_stack_wellformed : pas de double-occupation et pas de trous.---------------------
*------------- tn_condition_occupancy : si le paquet est à (node,pos,h) alors la case pos,h est occupée.------
*------------- tn_condition_actions : encode les opérations transmit/push/pop comme implications logiques.----
*-------------------------------------------------------------------------------------------------------------
*------------------------------------------------------------------------------------------------------------
 *  @brief
 *  @param ctx The solver context.
 * @param network.
 * @param length la longueur du chemin.
 * @return Z3_ast
 * ----------------- implementation du condition initial et final -------------------------------------------
 * ------------------- Condition initiale : on commence au nœud initial avec une pile vide (hauteur = 0) ------
 * ------------------ Condition finale : on termine au nœud final avec une pile vide (hauteur = 0)------------
 */

Z3_ast tn_condition_initial_and_final(Z3_context ctx, const TunnelNetwork network, int length)
{
    int N = tn_get_num_nodes(network);
    int H = get_stack_size(length);
    int init = tn_get_initial(network);

    // liste dynamique , maximum N*H contraintes
    Z3_ast *init_list = malloc(sizeof(Z3_ast) * (N * H + 1));
    int idx = 0;

    // x_(init,0,0) est vrai 
    init_list[idx++] = tn_path_variable(ctx, init, 0, 0);

    // etvtoutes les autres paires (node, height) à pos 0 sont fausses 
    for (int n = 0; n < N; ++n) {
        for (int h = 0; h < H; ++h) {
            if (!(n == init && h == 0)) {
                init_list[idx++] = Z3_mk_not(ctx, tn_path_variable(ctx, n, 0, h));
            }
        }
    }
    Z3_ast init_form = Z3_mk_and(ctx, idx, init_list);
    free(init_list);

   
    int fin = tn_get_final(network);
    Z3_ast *final_list = malloc(sizeof(Z3_ast) * (N * H + 1));
    int idxf = 0;

    final_list[idxf++] = tn_path_variable(ctx, fin, length, 0);

    for (int n = 0; n < N; ++n) {
        for (int h = 0; h < H; ++h) {
            if (!(n == fin && h == 0)) {
                final_list[idxf++] = Z3_mk_not(ctx, tn_path_variable(ctx, n, length, h));
            }
        }
    }
    Z3_ast final_form = Z3_mk_and(ctx, idxf, final_list);
    free(final_list);

    Z3_ast both[2] = {init_form, final_form};
    return Z3_mk_and(ctx, 2, both);
}


/**
* @brief
* @param ctx The solver context.
 * @param network.
 * @param length la longueur du chemin.
 * @return Z3_ast
 * -------------------------------- Unicité à chaque position ----------------------------------------
 * ------------------- a chaque position pos, exactement un couple (node,height) est vrai ------------
 */

Z3_ast tn_condition_uniqueness(Z3_context ctx, const TunnelNetwork network, int length)
{
    int N = tn_get_num_nodes(network);
    int H = get_stack_size(length);

    // Nous  accumulons les conjonctions dans un tableau dynamique 
    int est_upper = (length + 1) * (1 + (N * H) + (N * H * (N * H - 1) / 2));
    Z3_ast *conjs = malloc(sizeof(Z3_ast) * est_upper);
    int ci = 0;

    for (int pos = 0; pos <= length; ++pos) {
        // au moins un : OR_(n,h) x_(n,pos,h)
        //X(n1​,pos,h1​)∨X(n2​,pos,h2​)∨⋯∨X(nN​,pos,hH​)
        Z3_ast *or_args = malloc(sizeof(Z3_ast) * (N * H));
        int oi = 0;
        for (int n = 0; n < N; ++n)
            for (int h = 0; h < H; ++h)
                or_args[oi++] = tn_path_variable(ctx, n, pos, h);
        conjs[ci++] = Z3_mk_or(ctx, oi, or_args);
        free(or_args);

        // au plus un : pour chaque paire distincte i<j on interdit (vi and vj) 
        for (int n1 = 0; n1 < N; ++n1) {
            for (int h1 = 0; h1 < H; ++h1) {
                for (int n2 = n1; n2 < N; ++n2) {
                    int h2start = (n1 == n2) ? h1 + 1 : 0; //on evite les doublons (i,j) et (j,i)
                    for (int h2 = h2start; h2 < H; ++h2) {
                        //¬(X(n1​,pos,h1​)∧X(n2​,pos,h2​))
                        Z3_ast a = tn_path_variable(ctx, n1, pos, h1);
                        Z3_ast b = tn_path_variable(ctx, n2, pos, h2);
                        Z3_ast both = Z3_mk_and(ctx, 2, (Z3_ast[]){a, b});
                        conjs[ci++] = Z3_mk_not(ctx, both);
                    }
                }
            }
        }
    }

    Z3_ast result = Z3_mk_and(ctx, ci, conjs);
    free(conjs);
    return result;
}


/**
 * @brief
* @param ctx The solver context.
 * @param network.
 * @param length la longueur du chemin.
 * @return Z3_ast
 * -------------------------------- des arêtes bien definie ----------------------------------------
 * ------------------ Si on est au nœud u a pos, alors le nœud v a pos+1 doit être un voisin. ------------*/

Z3_ast tn_condition_edges(Z3_context ctx, const TunnelNetwork network, int length)
{
    int N = tn_get_num_nodes(network);
    int H = get_stack_size(length);

    int est_upper = length * N * H * (N * H + 1);
    Z3_ast *conjs = malloc(sizeof(Z3_ast) * est_upper);
    int ci = 0;

    for (int pos = 0; pos < length; ++pos) {
        for (int u = 0; u < N; ++u) {
            for (int h = 0; h < H; ++h) {
                Z3_ast premise = tn_path_variable(ctx, u, pos, h);

                // contruction la disjonction des positions possibles au pas suivant 
                Z3_ast *nexts = malloc(sizeof(Z3_ast) * (N * H));
                int ni = 0;
                for (int v = 0; v < N; ++v) {
                    if (!tn_has_edge_wrapper(network, u, v)) continue;
                    for (int hp = 0; hp < H; ++hp) {
                        nexts[ni++] = tn_path_variable(ctx, v, pos + 1, hp);
                    }
                }

                if (ni == 0) {
                    conjs[ci++] = Z3_mk_not(ctx, premise);
                    free(nexts);
                    continue;
                }

                Z3_ast allowed = Z3_mk_or(ctx, ni, nexts);
                free(nexts);

                //X(u,pos,h)⇒(X(v1​,pos+1,h1​)∨⋯∨X(vk​,pos+1,hm​))

                conjs[ci++] = Z3_mk_implies(ctx, premise, allowed);
            }
        }
    }

    Z3_ast result = Z3_mk_and(ctx, ci, conjs);
    free(conjs);
    return result;
}

/**
 * @brief
* @param ctx The solver context.
 * @param network.
 * @param length la longueur du chemin.
 * @return Z3_ast
 * -------------------------------- coherence du contenu du pile --------------------------------------------------
 * ----------------- interdit d’avoir a la fois une plaque IPv4 ET IPv6 au meme emplacement------------------------
 * ----------------- Si un niveau h est vide, alors tous les niveaux au-dessus doivent aussi être vides.------------*/

Z3_ast tn_condition_stack_wellformed(Z3_context ctx, int length)
{
    int H = get_stack_size(length);

    int est_upper = (length + 1) * (H + H * (H - 1) / 2);
    Z3_ast *conjs = malloc(sizeof(Z3_ast) * est_upper);
    int ci = 0;

    for (int pos = 0; pos <= length; ++pos) {
        for (int h = 0; h < H; ++h) {
            // ¬(4(pos,h)∧6(pos,h))
            Z3_ast both = Z3_mk_and(ctx, 2, (Z3_ast[]){tn_4_variable(ctx, pos, h), tn_6_variable(ctx, pos, h)});
            conjs[ci++] = Z3_mk_not(ctx, both);

            // si case h vide => toutes les cases >h vides 
            //empty(pos,h)=¬4(pos,h)∧¬6(pos,h)
            Z3_ast not4 = Z3_mk_not(ctx, tn_4_variable(ctx, pos, h));
            Z3_ast not6 = Z3_mk_not(ctx, tn_6_variable(ctx, pos, h));
            Z3_ast empty_h = Z3_mk_and(ctx, 2, (Z3_ast[]){not4, not6});
            for (int hp = h + 1; hp < H; ++hp) {
                Z3_ast not4p = Z3_mk_not(ctx, tn_4_variable(ctx, pos, hp));
                Z3_ast not6p = Z3_mk_not(ctx, tn_6_variable(ctx, pos, hp));
                Z3_ast empty_hp = Z3_mk_and(ctx, 2, (Z3_ast[]){not4p, not6p});
                conjs[ci++] = Z3_mk_implies(ctx, empty_h, empty_hp);
            }
        }
    }

    Z3_ast result = Z3_mk_and(ctx, ci, conjs);
    free(conjs);
    return result;
}




/**
 * @brief
* @param ctx The solver context.
 * @param network.
 * @param length la longueur du chemin.
 * @return Z3_ast
 * ----------- Si x(n,pos,h) est vrai alors la cellule (pos,h) est occupée par (y4 ou y6).
 * ------------------ Ceci garantit l'absence d'incohérence ------------------------------*/

Z3_ast tn_condition_occupancy(Z3_context ctx, const TunnelNetwork network, int length)
{
    int N = tn_get_num_nodes(network);
    int H = get_stack_size(length);

    int est_upper = (length + 1) * (N * H);
    Z3_ast *conjs = malloc(sizeof(Z3_ast) * est_upper);
    int ci = 0;

    for (int pos = 0; pos <= length; ++pos) {
        for (int h = 0; h < H; ++h) {
            //occ(pos,h)=4(pos,h)∨6(pos,h)
            Z3_ast occ = Z3_mk_or(ctx, 2, (Z3_ast[]){tn_4_variable(ctx, pos, h), tn_6_variable(ctx, pos, h)});
            for (int n = 0; n < N; ++n) {
                Z3_ast nth = tn_path_variable(ctx, n, pos, h);
                //x(n,pos,h)⇒occ(pos,h)
                conjs[ci++] = Z3_mk_implies(ctx, nth, occ);
            }
        }
    }

    Z3_ast result = Z3_mk_and(ctx, ci, conjs);
    free(conjs);
    return result;
}

/**
 * @brief
* @param ctx The solver context.
 * @param network.
 * @param length la longueur du chemin.
 * @return Z3_ast
 * ----------------- Conditions d’action (transmit/push/pop) --------------------------
 * ------------------ Chaque action impose une relation entre :------------------------- 
 * ----------------- node courant, node suivant, hauteur, contenu de pile 
 */
Z3_ast tn_condition_actions(Z3_context ctx, const TunnelNetwork network, int length)
{
    int N = tn_get_num_nodes(network);
    int H = get_stack_size(length);

    int est_upper = length * N * H * (N * H) * 2 + 1000;
    Z3_ast *conjs = malloc(sizeof(Z3_ast) * est_upper);
    int ci = 0;

    for (int pos = 0; pos < length; ++pos) {
        for (int n = 0; n < N; ++n) {
            for (int h = 0; h < H; ++h) {

                Z3_ast cur = tn_path_variable(ctx, n, pos, h);

                /* itèration sur toutes les paires (m, hp) possibles pour la position pos+1.
                   pour chaque paire on construit une implication avec l'antécédent */
                for (int m = 0; m < N; ++m) {
                    for (int hp = 0; hp < H; ++hp) {
                        Z3_ast nxt = tn_path_variable(ctx, m, pos + 1, hp);
                        //cur(n,pos,h)∧nxt(m,pos+1,hp)
                        Z3_ast antecedent = Z3_mk_and(ctx, 2, (Z3_ast[]){cur, nxt});

                        // construire les cas permis
                        Z3_ast cases[16];
                        int nc = 0;

                        // --- TRANSMIT (hp == h) ---
                        if (hp == h) {
                            if (tn_node_has_action(network, n, transmit_4)) {
                                // pos,h == 4 && pos+1,h == 4 
                                Z3_ast a = Z3_mk_and(ctx, 2, (Z3_ast[]){tn_4_variable(ctx, pos, h), tn_4_variable(ctx, pos + 1, h)});
                                cases[nc++] = a;
                            }
                            if (tn_node_has_action(network, n, transmit_6)) {
                                Z3_ast a = Z3_mk_and(ctx, 2, (Z3_ast[]){tn_6_variable(ctx, pos, h), tn_6_variable(ctx, pos + 1, h)});
                                cases[nc++] = a;
                            }
                        }

                        /* --- PUSH (hp == h + 1) --- */
                        if (hp == h + 1 && hp < H) {
                            // 4 possibilités (a,b) ∈ {4,6} × {4,6} */
                            if (tn_node_has_action(network, n, push_4_4)) {
                                // pos,h == 4 ; pos+1,h == 4 (below) ; pos+1,h+1 == 4 (new top) 
                                Z3_ast c = Z3_mk_and(ctx, 3, (Z3_ast[]){tn_4_variable(ctx, pos, h), tn_4_variable(ctx, pos + 1, h), tn_4_variable(ctx, pos + 1, hp)});
                                cases[nc++] = c;
                            }
                            if (tn_node_has_action(network, n, push_4_6)) {
                                Z3_ast c = Z3_mk_and(ctx, 3, (Z3_ast[]){tn_4_variable(ctx, pos, h), tn_4_variable(ctx, pos + 1, h), tn_6_variable(ctx, pos + 1, hp)});
                                cases[nc++] = c;
                            }
                            if (tn_node_has_action(network, n, push_6_4)) {
                                Z3_ast c = Z3_mk_and(ctx, 3, (Z3_ast[]){tn_6_variable(ctx, pos, h), tn_4_variable(ctx, pos + 1, h), tn_4_variable(ctx, pos + 1, hp)});
                                cases[nc++] = c;
                            }
                            if (tn_node_has_action(network, n, push_6_6)) {
                                Z3_ast c = Z3_mk_and(ctx, 3, (Z3_ast[]){tn_6_variable(ctx, pos, h), tn_6_variable(ctx, pos + 1, h), tn_6_variable(ctx, pos + 1, hp)});
                                cases[nc++] = c;
                            }
                        }

                        // --- POP (hp == h - 1) ---
                        if (hp + 1 == h && h >= 1) {
                            // pop supprimme top b
                            if (tn_node_has_action(network, n, pop_4_4)) {
                                // top b = 4 at pos,h ; below a = 4 at pos,h-1 ; new top at pos+1,h-1 = 4 
                                Z3_ast c = Z3_mk_and(ctx, 3, (Z3_ast[]){tn_4_variable(ctx, pos, h), tn_4_variable(ctx, pos, h - 1), tn_4_variable(ctx, pos + 1, hp)});
                                cases[nc++] = c;
                            }
                            if (tn_node_has_action(network, n, pop_4_6)) {
                                // pop_4_6 means below a=4, top b=6 
                                Z3_ast c = Z3_mk_and(ctx, 3, (Z3_ast[]){tn_6_variable(ctx, pos, h), tn_4_variable(ctx, pos, h - 1), tn_4_variable(ctx, pos + 1, hp)});
                                cases[nc++] = c;
                            }
                            if (tn_node_has_action(network, n, pop_6_4)) {
                                Z3_ast c = Z3_mk_and(ctx, 3, (Z3_ast[]){tn_4_variable(ctx, pos, h), tn_6_variable(ctx, pos, h - 1), tn_6_variable(ctx, pos + 1, hp)});
                                cases[nc++] = c;
                            }
                            if (tn_node_has_action(network, n, pop_6_6)) {
                                Z3_ast c = Z3_mk_and(ctx, 3, (Z3_ast[]){tn_6_variable(ctx, pos, h), tn_6_variable(ctx, pos, h - 1), tn_6_variable(ctx, pos + 1, hp)});
                                cases[nc++] = c;
                            }
                        }

                        // Si aucune case permise -> interdire l'antécédent
                        if (nc == 0) {
                            conjs[ci++] = Z3_mk_not(ctx, antecedent);
                        } else {
                            Z3_ast disj = Z3_mk_or(ctx, nc, cases);
                            conjs[ci++] = Z3_mk_implies(ctx, antecedent, disj);
                        }
                    } 
                }     
            }        
        }             
    }                 

    Z3_ast result = Z3_mk_and(ctx, ci, conjs);
    free(conjs);
    return result;
}

/**
 * @brief
* @param ctx The solver context.
 * @param network.
 * @param length la longueur du chemin.
 * @return Z3_ast
 * -----------------------------------------------------------------------------------------------------
*-----construction complète de la formule Z3 représentant la réduction TUNNEL -> SAT. -------------------
*------------------- -----------------------------------------------------------------------------------
 *  - initial/final
 *  - unicité
 *  - adjacency
 *  - cohérence pile (well-formed)
 *  - occupancy (si position alors cellule occupée)
 *  - actions (transmit/push/pop)
 */

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    assert(length >= 1);

    Z3_ast parts[6];
    int p = 0;

    parts[p++] = tn_condition_initial_and_final(ctx, network, length);
    parts[p++] = tn_condition_uniqueness(ctx, network, length);
    parts[p++] = tn_condition_edges(ctx, network, length);
    parts[p++] = tn_condition_stack_wellformed(ctx, length);
    parts[p++] = tn_condition_occupancy(ctx, network, length);
    parts[p++] = tn_condition_actions(ctx, network, length);

    return Z3_mk_and(ctx, p, parts);
}


void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound; pos++)
    {
        int src = -1;
        int src_height = -1;
        int tgt = -1;
        int tgt_height = -1;
        for (int n = 0; n < num_nodes; n++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos, height)))
                {
                    src = n;
                    src_height = height;
                }
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos + 1, height)))
                {
                    tgt = n;
                    tgt_height = height;
                }
            }
        }
        int action = 0;
        if (src_height == tgt_height)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                action = transmit_4;
            else
                action = transmit_6;
        }
        else if (src_height == tgt_height - 1)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = push_4_4;
                else
                    action = push_4_6;
            }
            else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                action = push_6_4;
            else
                action = push_6_6;
        }
        else if (src_height == tgt_height + 1)
        {
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                {
                    if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                        action = pop_4_4;
                    else
                        action = pop_6_4;
                }
                else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = pop_4_6;
                else
                    action = pop_6_6;
            }
        }
        path[pos] = tn_step_create(action, src, tgt);
    }
}

void tn_print_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound + 1; pos++)
    {
        printf("At pos %d:\nState: ", pos);
        int num_seen = 0;
        for (int node = 0; node < num_nodes; node++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, node, pos, height)))
                {
                    printf("(%s,%d) ", tn_get_node_name(network, node), height);
                    num_seen++;
                }
            }
        }
        if (num_seen == 0)
            printf("No node at that position !\n");
        else
            printf("\n");
        if (num_seen > 1)
            printf("Several pair node,height!\n");
        printf("Stack: ");
        bool misdefined = false;
        bool above_top = false;
        for (int height = 0; height < stack_size; height++)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, height)))
            {
                if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
                {
                    printf("|X");
                    misdefined = true;
                }
                else
                {
                    printf("|4");
                    if (above_top)
                        misdefined = true;
                }
            }
            else if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
            {
                printf("|6");
                if (above_top)
                    misdefined = true;
            }
            else
            {
                printf("| ");
                above_top = true;
            }
        }
        printf("\n");
        if (misdefined)
            printf("Warning: ill-defined stack\n");
    }
    return;
}