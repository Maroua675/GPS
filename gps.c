#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// --- CONSTANTES ET DEFINITIONS ---
#define MAX_STR 50       // Taille max d'un mot
#define MAX_FACTS 100    // Nombre max de faits
#define MAX_RULES 50     // Nombre max de règles
#define MAX_DEPTH 1000   // Profondeur max de recherche (taille de la mémoire)

typedef char String[MAX_STR];

// Structure pour une Règle
typedef struct {
    String name;
    String preconds[MAX_FACTS];
    int num_preconds;
    String adds[MAX_FACTS];
    int num_adds;
    String dels[MAX_FACTS];
    int num_dels;
} Rule;

// Structure pour un État (Mémoire)
typedef struct {
    String facts[MAX_FACTS];
    int num_facts;
    int next_rule_index; // IR : L'indice de la prochaine règle à tester pour cet état
    int rule_used_to_get_here; // Pour l'affichage final
} State;

// Variables Globales (Base de données du problème)
String initial_facts[MAX_FACTS];
int num_initial_facts = 0;

String goal_facts[MAX_FACTS];
int num_goal_facts = 0;

Rule rules[MAX_RULES];
int num_rules = 0;

// --- FONCTIONS UTILITAIRES ---

// Fonction fournie dans le sujet pour découper les lignes
int parseLine(char source[], String cible[]) {
    int n = 0;
    char *token = strtok(source, ":"); // ignorer ce qui est avant ':'
    token = strtok(NULL, ":"); // la partie après ':'
    if (!token) return 0;

    char *fact = strtok(token, ",");
    while (fact != NULL) {
        // enlever les espaces au début et à la fin
        while(*fact == ' ') fact++;
        char *end = fact + strlen(fact) - 1;
        while(end > fact && (*end == ' ' || *end == '\n' || *end == '\r')) {
            *end = '\0';
            end--;
        }

        if (strlen(fact) > 0) {
            strcpy(cible[n], fact);
            n++;
        }
        fact = strtok(NULL, ",");
    }
    return n;
}

// Vérifie si un fait est présent dans une liste
int hasFact(String list[], int count, char* fact) {
    for (int i = 0; i < count; i++) {
        if (strcmp(list[i], fact) == 0) return 1;
    }
    return 0;
}

// Ajoute un fait s'il n'existe pas déjà
void addFact(String list[], int *count, char* fact) {
    if (!hasFact(list, *count, fact) && *count < MAX_FACTS) {
        strcpy(list[*count], fact);
        (*count)++;
    }
}

// Supprime un fait
void removeFact(String list[], int *count, char* fact) {
    for (int i = 0; i < *count; i++) {
        if (strcmp(list[i], fact) == 0) {
            // Remplacer par le dernier pour combler le trou
            strcpy(list[i], list[*count - 1]);
            (*count)--;
            i--; // revérifier la position au cas où doublon (rare)
        }
    }
}

// --- CHARGEMENT DES DONNÉES (Partie 1) ---

void loadProblem(const char* filename) {
    FILE* file = fopen(filename, "r");
    if (!file) {
        perror("Erreur ouverture fichier");
        exit(1);
    }

    char line[512];
    int mode = 0; // 0:none, 1:rule

    while (fgets(line, sizeof(line), file)) {

        // Nettoyage fin de ligne
        line[strcspn(line, "\r\n")] = 0;

        // Ignorer lignes vides
        if (strlen(line) == 0) continue;

        // Séparateur
        if (strncmp(line, "****", 4) == 0) {
            mode = 0;
            continue;
        }

        // ---------- CHANGED ----------
        // start: au lieu de FACTS:
        if (strncmp(line, "start:", 6) == 0) {
            num_initial_facts = parseLine(line, initial_facts);
        }

        // ---------- CHANGED ----------
        // finish: au lieu de GOALS:
        else if (strncmp(line, "finish:", 7) == 0) {
            num_goal_facts = parseLine(line, goal_facts);
        }

        // ---------- CHANGED ----------
        // action: au lieu de RULE:
        else if (strncmp(line, "action:", 7) == 0) {
            mode = 1;

            String temp[1];
            parseLine(line, temp);
            strcpy(rules[num_rules].name, temp[0]);

            rules[num_rules].num_preconds = 0;
            rules[num_rules].num_adds = 0;
            rules[num_rules].num_dels = 0;
        }

        // ---------- CHANGED ----------
        else if (mode == 1) {

            // preconds: au lieu de PRECONDS:
            if (strncmp(line, "preconds:", 9) == 0) {
                rules[num_rules].num_preconds =
                    parseLine(line, rules[num_rules].preconds);
            }

            // add: au lieu de ADD:
            else if (strncmp(line, "add:", 4) == 0) {
                rules[num_rules].num_adds =
                    parseLine(line, rules[num_rules].adds);
            }

            // delete: au lieu de DEL:
            else if (strncmp(line, "delete:", 7) == 0) {
                rules[num_rules].num_dels =
                    parseLine(line, rules[num_rules].dels);

                // Fin de règle
                num_rules++;
            }
        }
    }

    fclose(file);

    printf("Chargement termine: %d Faits initiaux, %d Buts, %d Regles.\n",
           num_initial_facts, num_goal_facts, num_rules);
}

// --- MOTEUR DE RAISONNEMENT (Parties 2 et 3) ---

// Vérifie si une règle est applicable sur un état donné
int isApplicable(Rule* r, State* s) {
    for (int i = 0; i < r->num_preconds; i++) {
        if (!hasFact(s->facts, s->num_facts, r->preconds[i])) {
            return 0; // Une précondition manque
        }
    }
    return 1;
}

// Vérifie si le but est atteint
int goalsAchieved(State* s) {
    for (int i = 0; i < num_goal_facts; i++) {
        if (!hasFact(s->facts, s->num_facts, goal_facts[i])) {
            return 0; // Un but manque
        }
    }
    return 1;
}

// Vérifie si deux états sont identiques (pour éviter les boucles infinies simples A->B->A)
int isSameState(State* s1, State* s2) {
    if (s1->num_facts != s2->num_facts) return 0;
    // On vérifie que chaque fait de s1 est dans s2
    for(int i=0; i < s1->num_facts; i++) {
        if(!hasFact(s2->facts, s2->num_facts, s1->facts[i])) return 0;
    }
    return 1;
}

// Fonction principale de résolution (Backtracking)
void solve() {
    State memory[MAX_DEPTH];
    int depth = 0;

    // 1. Initialisation de l'état initial
    memory[0].num_facts = num_initial_facts;
    for(int i=0; i<num_initial_facts; i++) strcpy(memory[0].facts[i], initial_facts[i]);
    memory[0].next_rule_index = 0;
    memory[0].rule_used_to_get_here = -1;

    int possible = 1;
    int steps = 0;

    printf("\n--- Debut du raisonnement (Backtracking) ---\n");

    // Tant que buts non atteints ET possible
    while (!goalsAchieved(&memory[depth]) && possible) {
        steps++;
        int rule_found = 0;
        State *current = &memory[depth];

        // Chercher une règle applicable à partir de IR (next_rule_index)
        for (int i = current->next_rule_index; i < num_rules; i++) {
            if (isApplicable(&rules[i], current)) {
                
                // Préparer le nouvel état
                State newState;
                newState.num_facts = current->num_facts;
                // Copier les faits
                for(int k=0; k<current->num_facts; k++) strcpy(newState.facts[k], current->facts[k]);
                
                // Appliquer DEL
                for(int k=0; k<rules[i].num_dels; k++) removeFact(newState.facts, &newState.num_facts, rules[i].dels[k]);
                // Appliquer ADD
                for(int k=0; k<rules[i].num_adds; k++) addFact(newState.facts, &newState.num_facts, rules[i].adds[k]);
                
                // --- Anti-Loop Check (Simple) ---
                // Vérifier si ce nouvel état existe déjà dans le chemin actuel (ancêtres)
                int already_seen = 0;
                for(int k=0; k<=depth; k++) {
                    if(isSameState(&memory[k], &newState)) {
                        already_seen = 1; 
                        break;
                    }
                }

                if(already_seen) {
                    // Si cet état ramène en arrière, on ignore cette règle et on continue la boucle for
                    continue; 
                }

                // Si on est ici, la règle est valide et ne boucle pas
                
                // Sauvegarder où on s'est arrêté pour le backtrack futur
                current->next_rule_index = i + 1;

                // Passer au nouvel état (Empiler)
                depth++;
                if (depth >= MAX_DEPTH) {
                    printf("Erreur: Profondeur maximale atteinte !\n");
                    return;
                }

                memory[depth] = newState;
                memory[depth].next_rule_index = 0; // IR repasse à 0 pour le nouvel état
                memory[depth].rule_used_to_get_here = i;

                rule_found = 1;
                // printf("Applique regle %s -> Profondeur %d\n", rules[i].name, depth); // Debug
                break; // On sort de la boucle de recherche de règle pour traiter le nouvel état
            }
        }

        if (!rule_found) {
            // BACKTRACK
            if (depth > 0) {
                // On dépile (l'état courant est oublié, on revient au précédent)
                // L'état précédent reprendra sa boucle for là où il s'était arrêté (grâce à next_rule_index)
                depth--;
                // printf("Backtrack vers profondeur %d\n", depth); // Debug
            } else {
                possible = 0; // Plus d'états précédents, solution impossible
            }
        }
    }

    // --- Affichage du résultat ---
    if (possible) {
        printf("\nVICTOIRE ! But atteint en %d etapes de calcul.\n", steps);
        printf("Chemin de la solution :\n");
        for (int i = 1; i <= depth; i++) {
            printf("%d. %s\n", i, rules[memory[i].rule_used_to_get_here].name);
        }
        
        printf("\nFaits finaux : ");
        for(int i=0; i<memory[depth].num_facts; i++) printf("%s ", memory[depth].facts[i]);
        printf("\n");

    } else {
        printf("\nECHEC. Impossible de trouver une solution.\n");
    }
}

// --- MAIN ---

int main() {
    char filename[100];
    printf("Entrez le nom du fichier probleme (ex: monkey.txt / school.txt / blocks.txt ou wolf_goat_cabbage.txt / ) : ");
    scanf("%s", filename);

    loadProblem(filename);
    
    // Affichage de vérification
    printf("Faits initiaux: ");
    for(int i=0; i<num_initial_facts; i++) printf("%s ", initial_facts[i]);
    printf("\nButs: ");
    for(int i=0; i<num_goal_facts; i++) printf("%s ", goal_facts[i]);
    printf("\n");

    solve();

    return 0;
}