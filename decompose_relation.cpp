
#include <bitset>
#include <algorithm>
#include <iostream>
#include "decompose_relation.h"

using namespace std;

bool decomposeRelationTrivial(const Relation& relation, unsigned int n) {
    return false;
}


void generate_subrelations(const Relation& R, std::vector<Relation>& subrelations) {

    subrelations.clear();
    subrelations.emplace_back(); // Add the empty relation as a subrelation

    for (size_t i = 1; i < (1ull << R.size()); i++) {
        //cout<< "i = " << i  << endl;
        vector<bool> bools(R.size());
        for (size_t j = 0; j < R.size(); j++) {
            bools[j] = (i >> j) & 1;
            cout << bools[j] << " ";
        }
        Relation subrelation;

        for (int j = 0; j < R.size(); j++) {
            if (bools[j]) {
                subrelation.push_back(R[j]);
            }
        }
        for (RelationElement re : subrelation) {
            cout<< "(" << re.first << ", " << re.second << "), ";
        }
        cout << endl;
        // \forall x \forall y \forall z (Ri(x,y) & Ri(x,z) -> Ri(y,z))
        if (satisfied(subrelation)) {
            cout<< "added with i = " << i <<endl;
            subrelations.push_back(subrelation);
        }
    }

    // Sort the vector of subrelations by size
    std::sort(subrelations.begin(), subrelations.end(), [](const Relation& a, const Relation& b) {
        return a.size() < b.size();
    });
}
//forall x \forall y \forall z (Ri(x,y) & Ri(x,z) -> Ri(y,z))
bool satisfied(const Relation& R) {
    for (const auto& x : R) {
        cout<< "x: (" << x.first << ", " << x.second << "), ";
        for (const auto& y : R) {
            cout<< "y: (" << y.first << ", " << y.second << "), ";
            if (x.first == y.first) {
                bool found = false;
                for (const auto& z : R) {
                    cout<< "z: (" << z.first << ", " << z.second << "), ";
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

int main() {
    // Example usage of generate_subrelations
    Relation R = {{1, 1}, {1,2}, {2, 1}, {2, 2}, {2, 3}, {1, 3}};
    std::vector<Relation> subrelations;
    generate_subrelations(R, subrelations);
    std::cout << "Number of subrelations: " << subrelations.size() << std::endl;
    for (const auto& S : subrelations) {
        std::cout << "subrelation" << std::endl;
        for (const auto& x : S) {
            std::cout << "(" << x.first << "," << x.second << ") ";
        }
        std::cout << std::endl;
    }
    return 0;
}

