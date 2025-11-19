#include "TunnelBF.h"
#include "TunnelNetwork.h"
#include <stdlib.h>
#include <stdio.h>

//cette fonction sert à tester si une action est possible en fonction de l'état actuelle de la pile :
    //si oui, elle effectue cette action en mettant a jour "stack" et "stackHeight" et renvoi true
    //sinon, elle renvoi false => action non possible sur la stack
bool doActionOnStack(int action, int stack[], int* stackHeight){
    //printf("do : stackHeight = %d ; stack[stackHeig-1] = %d ; action = %d\n", *stackHeight, stack[*(stackHeight)-1], action);
    
    //switch case un peu redondant pour chaque action possible
    switch (action) {
        case transmit_4:
            return (stack[*(stackHeight)-1] == 4);

        case transmit_6:
            return (stack[*(stackHeight)-1] == 6);

        case push_4_4:
            if(stack[*(stackHeight)-1] == 4){
                (*stackHeight)++;
                stack[*(stackHeight)-1] = 4;
                return true;
            } else {
                return false;
            }

        case push_4_6:
            if(stack[*(stackHeight)-1] == 4){
                (*stackHeight)++;
                stack[*(stackHeight)-1] = 6;
                return true;
            } else {
                return false;
            }

        case push_6_4:
            if(stack[*(stackHeight)-1] == 6){
                (*stackHeight)++;
                stack[*(stackHeight)-1] = 4;
                return true;
            } else {
                return false;
            }

        case push_6_6:
            if(stack[*(stackHeight)-1] == 6){
                (*stackHeight)++;
                stack[*(stackHeight)-1] = 6;
                return true;
            } else {
                return false;
            }

        case pop_4_4:
            if(*stackHeight >= 2 && stack[*(stackHeight)-1] == 4 && stack[*(stackHeight)-2] == 4){
                stack[*(stackHeight)-1] = -1;
                (*stackHeight)--;
                return true;
            } else {
                return false;
            }

        case pop_4_6:
            if(*stackHeight >= 2 && stack[*(stackHeight)-1] == 6 && stack[*(stackHeight)-2] == 4){
                stack[*(stackHeight)-1] = -1;
                (*stackHeight)--;
                return true;
            } else {
                return false;
            }

        case pop_6_4:
            if(*stackHeight >= 2 && stack[*(stackHeight)-1] == 4 && stack[*(stackHeight)-2] == 6){
                stack[*(stackHeight)-1] = -1;
                (*stackHeight)--;
                return true;
            } else {
                return false;
            }

        case pop_6_6:
            if(*stackHeight >= 2 && stack[*(stackHeight)-1] == 6 && stack[*(stackHeight)-2] == 6){
                stack[*(stackHeight)-1] = -1;
                (*stackHeight)--;
                return true;
            } else {
                return false;
            }

        default:
            printf("Erreur dans doAction\n");
            exit(EXIT_FAILURE);
    }    
}

//undoActionOnStack() annule une action donné en parametre sur la stack
//pas de test de verification d'action inverse possible sur la pile car non nécessaire ...
// => elle sera toujours appelé apres un appel de doActionOnStack() pour la meme "action"
void undoActionOnStack(int action, int stack[], int* stackHeight){
    //printf("undo : stackHeight = %d ; stack[stackHeig-1] = %d ; action = %d\n", *stackHeight, stack[*(stackHeight)-1], action);
    
    //pas besoin de case transmit car rien a faire
    switch (action) {
        case push_4_4:
            stack[*(stackHeight)-1] = -1;
            (*stackHeight)--;
            break;

        case push_4_6:
            stack[*(stackHeight)-1] = -1;
            (*stackHeight)--;
            break;

        case push_6_4:
            stack[*(stackHeight)-1] = -1;
            (*stackHeight)--;
            break;

        case push_6_6:
            stack[*(stackHeight)-1] = -1;
            (*stackHeight)--;
            break;

        case pop_4_4:
            (*stackHeight)++;
            stack[*(stackHeight)-1] = 4;
            break;

        case pop_4_6:
            (*stackHeight)++;
            stack[*(stackHeight)-1] = 6;
            break;

        case pop_6_4:
            (*stackHeight)++;
            stack[*(stackHeight)-1] = 4;
            break;

        case pop_6_6:
            (*stackHeight)++;
            stack[*(stackHeight)-1] = 6;
            break;
    }
}

//fonction auxiliaire servant à explorer le graphe "network", pour trouver et stocker dans "path" ...
// un chemin valide de taille "length" qui respectera les condition de pile
int tn_brute_force_aux(TunnelNetwork network, int length, tn_step *path, int stack[], int* stackHeight, int pas, int node){
    //printf("Pas = %d, node = %d\n", pas, node);
    
    if(pas == length){
        if(node == tn_get_final(network)){
            if(*stackHeight == 1 && stack[*(stackHeight)-1] == 4){
                //on a trouvé un chemin valide, respectant les conditions de pile, sa longeur demandé
                //et on est sur le noeud final du graphe
                return pas;
            } else {
                //on est sur le neoud final du graphe pour un chemin de bonne longueur, ... 
                // mais les conditions de piles ne sont pas respectés
                return -1;
            }
        } else {
            //le chemin a la taille demandé mais le noeud actuelle n'est pas le neoud final du graphe
            return -1;
        }
    } else if(pas > length){
        //on a depassé la taille de chemin demandé
        return -1;
    }

    //on explore les sommet n pour trouver ceux qui sont lié au noeud actuel "node"
    for(int n=0; n<tn_get_num_nodes(network); n++){
        if(tn_is_edge(network, node, n)){
            //on explore les action que peuxc faire du noeud actuel "node" avec le mask
            //ces action que possede le noeud actuelle devront etre compatible avec l'état actuelle de la stack

            for(int action=0; action<NumActions; action++){
                int mask = tn_get_actions(network, node);
                if((mask & (1 << action)) != 0 
                    && doActionOnStack(action, stack, stackHeight)){
                    //on applique l'action possible sur la stack, avec stackHeight possiblement mis a jour

                    //on ajouter a path le step actuelle
                    *(path + pas) = tn_step_create(action, node, n);

                    //on lance la recursion avec les parametre mis a jour
                    // (juste le pas car les variable de stack sont mise a jour dans doActionOnStack())
                    int res = tn_brute_force_aux(network, length, path, stack, stackHeight, pas+1, n);
                        
                    if(res != -1){
                        //la recursion a trouvé un chemin valide
                        //res contient un pas (forcement de longueur lenght)

                        return res;
                    } else {
                        //la recursion n'a pas trouvé de chemin valide

                        //on annule le pas ajouté
                        *(path + pas) = tn_step_empty();

                        //on annule l'action ajouté sur la pile 
                        undoActionOnStack(action, stack, stackHeight);
                    }
                }
            }
        }
    }

    //aucun chemin valide n'a été trouvé
    return -1;
}

//fonction qui tentera un brut force pour resoudre le probleme tunnel
//sert de fonction d'initialisation pour la fonction recursive auxiliaire
int tn_brute_force(TunnelNetwork network, int length, tn_step *path)
{
    //on va representer la stack par la tableau d'entier de taille (length/2)+1 
    //les valeurs possible sont :
        //-1 => espace vide
        //4 => protocole ipv4 empilé
        //6 => protocole ipv6 empilé
    //son indice 0 sera un protocole ipv4 et le reste des -1
    int maxTaillePile = (length/2)+1;
    int* stack = malloc(maxTaillePile * sizeof(int));
    if(stack == NULL){
        printf("Malloc failded\n");
        exit(EXIT_FAILURE);
    }
    *stack = 4;
    for(int i=1; i<maxTaillePile; i++){
        *(stack + i) = -1;
    }

    //la variable stackHeight represente elle le nombre d'element dans la stack actuelle
    //par default, elle sera de taille 1 avec un premier protocole ipv4 empilé (à l'indice 0)
    int* stackHeight = malloc(sizeof(int));
    if(stackHeight == NULL){
        printf("Malloc failded\n");
        exit(EXIT_FAILURE);
    }
    *stackHeight = 1;

    //node stock le numéro du noeu dans lequel on sera au fur et a mesure de l'algo (debute au 1er)
    int node = tn_get_initial(network);
    //pas servira a reprenter l'avancement dans le graphe => devra etre de taille length pour un chemin valide
    int pas = 0;

    //on lance la fonction recursive auxiliaire, et revoi son resultat
    int res = tn_brute_force_aux(network, length, path, stack, stackHeight, pas, node);

    free(stack);
    free(stackHeight);
    
    return res;
}