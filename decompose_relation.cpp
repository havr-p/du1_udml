
#include <bitset>
#include <algorithm>
#include <iostream>
#include <set>
#include <random>
#include <fstream>
#include <climits>
#include <unistd.h>
#include "decompose_relation.h"


using namespace std;

bool findUnions(const vector<Relation> &relations, uint n, const Relation &relation);
void generateSubrelations(const Relation& R, std::vector<Relation>& subrelations);
bool satisfied(const Relation& subrelation);
//literal representing fact that pair (x, y) is in subrelation Ri
int pairInSubrelationLiteral(int x, int y, int i, uint n) {
    return i * (n * n) + x * n + y + 1;
}
int q(int n, int x, int y, int osem) {
    return osem*n*n + x*n + y+1;
}


//generates cnf clause that represents fact that any pair (x, y) from relation R is in at least one of subrelation Ri
void ensureEachPairInSubrelation(const Relation& R, uint n, Cnf& cnf) {
    for (RelationElement re : R) {
        //add clause to cnf representing fact
        Clause clause;
        for (int i = 1; i <= 8; ++i) {
            clause.push_back(pairInSubrelationLiteral(re.first, re.second, i, n));
        }
        cnf.push_back(clause);
    }
}


bool findUnions(const vector<Relation> &relations, uint n, const Relation &relation) {
    vector<vector<Relation>> relation_combinations;
    vector<bool> presents(relations.size() - 8, false);
    presents.resize(relations.size(), true);
    do {
        vector<Relation> relation_combination;
        for (int i = 0; i < relations.size(); ++i) {
            if (presents[i]) {
                relation_combination.push_back(relations[i]);
            }
        }

        // check if there exists union
        bool valid = true;
            set<RelationElement> relation_union;
            for (const auto &rel: relation_combination) {
                relation_union.insert(rel.begin(), rel.end());
            }
            for (const auto &relationElement: relation) {
                if (relation_union.find(relationElement) == relation_union.end()) {
                    valid = false;
                    break;
                }
            }
        if (valid) {
            cout<<"relation combination\n";
            for (const Relation& r: relation_combination) {
                for (RelationElement re : r)
                    cout << "(" << re.first << ", " << re.second << "), ";
                cout<<endl;
            }
            cout<<"end of relation combination\n";
            for (RelationElement re: relation_union) {
                 cout << "(" << re.first << ", " << re.second << "), ";
            }
            cout<<endl;
            return true;
        }


    } while (std::next_permutation(presents.begin(), presents.end()));
    return false;
}


void generateSubrelations(const Relation &R, std::vector<Relation> &subrelations) {
    cout<<"generateSubrelations\n";

    subrelations.clear();
    subrelations.emplace_back();

    for (size_t i = 1; i < (1ull << R.size()); i++) {
        //cout<< "i = " << i  << endl;
        vector<bool> bools(R.size());
        for (size_t j = 0; j < R.size(); j++) {
            bools[j] = (i >> j) & 1;
            //cout << bools[j] << " ";
        }
        Relation subrelation;

        for (int j = 0; j < R.size(); j++) {
            if (bools[j]) {
                subrelation.push_back(R[j]);
            }
        }
        for (RelationElement re: subrelation) {
           // cout << "(" << re.first << ", " << re.second << "), ";
        }
        //cout << endl;
        // \forall x \forall y \forall z (Ri(x,y) & Ri(x,z) -> Ri(y,z))
        if (satisfied(subrelation)) {
            cout << "added with i = " << i << endl;
            subrelations.push_back(subrelation);
        }
    }

    //for time reducing
    std::sort(subrelations.begin(), subrelations.end(), [](const Relation &a, const Relation &b) {
        return a.size() < b.size();
    });
    cout<<"number of generated subrealtions = "<<subrelations.size()<<endl;
}

//forall x \forall y \forall z (Ri(x,y) & Ri(x,z) -> Ri(y,z))
bool satisfied(const Relation &R) {
    for (const auto &x: R) {
        for (const auto &y: R) {
            if (x.first == y.first) {
                bool found = false;
                for (const auto &z: R) {
                    if (z.first == x.second && z.second == y.second) {
                        found = true;
                        break;
                    }
                }
                if (!found) {
                    return false;
                }
            }
        }
    }
    return true;
}
bool decomposeRelationTrivial(const Relation &relation, unsigned int n) {
    vector<Relation> relations;
    generateSubrelations(relation, relations);
    cout << findUnions(relations, n, relation) << endl;
    return findUnions(relations, n, relation);
}

Cnf decomposeRelationToCNFNonBinary(const Relation& r, unsigned int n) {
    unsigned int s = r.size();
    Cnf cnf;

    ensureEachPairInSubrelation(r, n, cnf);

    for(int x = 0 ; x < n; x++) {   //vsetky moznosti aj co nie su
        for(int y = 0 ; y < n; y++) {
            for(int z = 0 ; z < n; z++) {
                for(int i = 0; i < 8; i++) {
                    Clause c2;
                    c2.push_back(-pairInSubrelationLiteral(x, y, i, n));
                    c2.push_back(-pairInSubrelationLiteral(x, z, i, n));
                    c2.push_back(pairInSubrelationLiteral(y, z, i, n));
                    cnf.push_back(c2);
                }
            }
        }
    }

    for(int i = 0; i < n; i++) {    //co nechceme
        for(int j = 0; j < n; j++) {
            for(int osem = 0; osem < 8; osem++) {
                bool jeTu = false;
                for(RelationElement rel : r){
                    if(rel.first == i && rel.second == j) {
                        jeTu = true;
                        break;
                    }
                }
                if(!jeTu) {
                    Clause c3;
                    //c3.push_back(-q(n, i, j, osem));
                    c3.push_back(-pairInSubrelationLiteral(i, j, osem, n));
                    cnf.push_back(c3);
                }
            }
        }
    }
    return cnf;
}

Cnf decomposeRelationToCNFBest(const Relation& r, unsigned int n) {
    unsigned int s = r.size();
    Cnf cnf;

    for (int i = 0; i < s; i++) {
        Clause c;
        for (int j = 0; j < 8; j++) {
            c.push_back(q(n, r[i].first, r[i].second, j));
        }
        cnf.push_back(c);
    }

    for (RelationElement it: r) {
        int x = it.first;
        int y = it.second;
        for (RelationElement it2: r) {
            if (x == it2.first) {
                bool found = false;
                int z = it2.second;

                for (RelationElement it3: r) {
                    if (y == it3.first && z == it3.second) {
                        found = true;
                        for (int i = 0; i < 8; i++) {
                            Clause c2;
                            c2.push_back(-q(n, x, y, i));
                            c2.push_back(-q(n, x, z, i));
                            c2.push_back(q(n, y, z, i));
                            cnf.push_back(c2);
                        }
                        break;
                    }
                }

                if (!found) {
                    for (int i = 0; i < 8; i++) {
                        Clause c3;
                        c3.push_back(-q(n, x, y, i));
                        c3.push_back(-q(n, x, z, i));
                        cnf.push_back(c3);
                    }
                }
            }
        }
    }

    return cnf;
}

// x + (n * y)

int main() {
    for(int i = 1 ; i < 11 ; i++){
        std::ofstream out("input.txt");
        const unsigned int n=25;
        const unsigned int p=2000; // probability p/10000
        const unsigned int seed=i;
        char path[PATH_MAX];
        if (getcwd(path, sizeof(path)) != NULL) {
            std::cout << "Current working directory: " << path << std::endl;
        }
        std::mt19937 gen(seed); //set seed
        std::uniform_int_distribution<> distrib(0, 9999);

        Relation r;
        for(int i=0; i<n; i++) {
            for(int j=0; j<n; j++) {
                if (i==j || distrib(gen)<p) {
                    r.emplace_back(i, j);
                }
            }
        }

        Cnf cnf = decomposeRelationToCNFBest(r, n);
        //Cnf cnf = decomposeRelationToCNFNonBinary(r, n);
        for(auto &clause : cnf) {
            for (auto &literal: clause) {
                out << literal << " ";
            }
            out << " 0" << std::endl;
        }

        //system("minisat vstup.txt decompose_relations.cpp");

        system(R"(/home/havr/CLionProjects/du1_udml/minisat input.txt decompose_relation.cpp)");

    }
    return 0;
}

