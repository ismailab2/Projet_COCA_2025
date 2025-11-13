#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"
#include <stdlib.h>

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

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    return Z3_mk_false(ctx);
}



/*les debut d'implementation des conditions de reduction des tunnels vers SAT
** chaque condition est implementé par une fonction expecifique a l'exception du 
**condition initial et final*/

/*----------------- implementation du condition initial et final -------------------------------------------
------------------- Condition initiale : on commence au nœud initial avec une pile vide (hauteur = 0) -------
------------------- Condition finale : on termine au nœud final avec une pile vide (hauteur = 0)------------*/

Z3_ast tn_condition_initial_and_final(Z3_context ctx, const TunnelNetwork network, int length){

    // nombres des noeuds du reseaux
    int nombre_noeud = tn_get_num_nodes(network);

    //la hauteur maximal
    int h_max = get_stack_size(length);

    // condition  initial
    int initial_noeud = tn_get_initial(network);

    // un tableau dynamique pour stocker les contraintes logiques Z3.
    Z3_ast *contrainte_initial = malloc(sizeof(Z3_ast)*nombre_noeud*h_max);

    int indice = 0;
    contrainte_initial[indice++]  = tn_path_variable(ctx,  initial_noeud,  0, 0);

    for(int n=0; n<nombre_noeud; n++){
        for(int h = 0 ; h<h_max; h++){
            if (!(n==initial_noeud && h ==0)){
                contrainte_initial[indice++]  = Z3_mk_not(ctx, tn_path_variable(ctx, n, 0, h));
            }
        }

    }

    Z3_ast init_formul = Z3_mk_and(ctx, indice, contrainte_initial);

    // 🔹 Libère la mémoire temporaire du tableau de contraintes.
    free(contrainte_initial);


    //condition final
        // noeud initial
    int final_noeud = tn_get_final(network);

    // un tableau dynamique pour stocker les contraintes logiques Z3.
    Z3_ast *contrainte_finale = malloc(sizeof(Z3_ast)*nombre_noeud*h_max);

    int indicef = 0;
    contrainte_finale[indicef++]  = tn_path_variable(ctx,  final_noeud,  0, 0);

    for(int n=0; n<nombre_noeud; n++){
        for(int h = 0 ; h<h_max; h++){
            if (!(n==final_noeud && h ==0)){
                contrainte_finale[indicef++]  = Z3_mk_not(ctx, tn_path_variable(ctx, n, 0, h));
            }
        }

    }

    Z3_ast final_formul = Z3_mk_and(ctx, indicef, contrainte_finale);

    free(contrainte_finale);

    Z3_ast cond_init_final[2] = {init_formul, final_formul};

    return Z3_mk_and(ctx, 2, cond_init_final);

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