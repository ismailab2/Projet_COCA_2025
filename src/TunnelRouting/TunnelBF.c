#include "TunnelBF.h"
#include "TunnelNetwork.h"
#include <stdlib.h>
#include <stdio.h>

bool isActionPossibleOnStack(int action, int stack[], int stackHeight){
    return true;
}

int tn_brute_force_rec(TunnelNetwork network, int length, tn_step *path, int stack[], int stackHeight, int pas, int node){
    //printf("Pas = %d, node = %d\n", pas, node);
    if(pas == length){
        //printf("oui\n");
        tn_print_path(network, path, length);
        if(node == tn_get_final(network)){
            if(stackHeight == 0){
                return pas;
            } else {
                return -1;
            }
        } else {
            return -1;
        }
    } else if(pas > length){
        return -1;
    }

    //on explore les sommet pour trouver ceux qui sont lié à node
    for(int n=0; n<tn_get_num_nodes(network); n++){
        if(tn_is_edge(network, node, n)){
            //on explore les action possible de node possible en fonction de la stack
            for(int action=0; action<NumActions; action++){
                int mask = tn_get_actions(network, node);
                if((mask & (1 << action)) != 0 
                    && isActionPossibleOnStack(action, stack, stackHeight)){
                    //on applique l'action sur la stack
                    //stack[stackHeight] = action;

                    //on ajouter a path le step actuelle
                    *(path + pas) = tn_step_create(action, node, n);

                    //on lance la recursion avec les parametre mis a jour
                    //int res = tn_brute_force_rec(network, length, path, stack, stackHeight+1, pas+1, n);
                    
                    //version sans gestion de stack pour le moment
                    int res = tn_brute_force_rec(network, length, path, stack, stackHeight, pas+1, n);

                    if(res != -1){
                        return res;
                    } else {
                        //stack[stackHeight] = -1;
                        *(path + pas) = tn_step_empty();
                    }

                }
            }
        }
    }

    return -1;
}

int tn_brute_force(TunnelNetwork network, int length, tn_step *path)
{
    /* Nous n’attendons pas que cette fonction soit implémentée pour la partie principale du projet.
    Néanmoins, si vous voulez tester vos idée pour un brute-force, vous pouvez le faire ici, ou même simplement tester diverses choses sur une instance : cette fonction sera appelée si vous lancez le programme avec l’option -B, et le contenu de path sera affiché (de la taille de l’entier renvoyé). */
    
    tn_print(network);

    printf("%d\n", length);

    int* stack = malloc(100 * sizeof(int)); //100 TO CHANGE
    for(int i=0; i<100; i++){
        *(stack + i) = -1;
    }
    int stackHeight = 0;

    int node = tn_get_initial(network);
    int pas = 0;

    int res = tn_brute_force_rec(network, length, path, stack, stackHeight, pas, node);

    free(stack);
    
    return res;
}