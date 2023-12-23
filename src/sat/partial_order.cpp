#include "partial_order.h"

#include <cvc5/cvc5.h>
#include <iostream>
#include <numeric>

#include "ipasir.h"

using namespace cvc5;

void generate_matching_formula(void* solver, sat_capsule & capsule, Model * htn, SOG* leafSOG, vector<vector<pair<int,int>>> & vars, MatchingData & matching){
	cout << "\n\npartial\n\n";
	//return;
	////////////////////////////////// matching variables
	matching.matchingPerLeaf.resize(leafSOG->numberOfVertices);
	matching.matchingPerPosition.resize(vars.size());
	matching.matchingPerPositionAMO.resize(vars.size());
	matching.vars = vars;
	matching.leafSOG = leafSOG;

	/*Solver *s = (Solver*)solver;
  	Sort intSort = s->getIntegerSort();
	std::vector<Term> rleafs;
	std::vector<Term> rpositions;

	rleafs.resize(leafSOG->numberOfVertices);
	rpositions.resize(vars.size());*/

	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		for (int lSucc : leafSOG->successorSet[l]){
			cout << lSucc;
		}
		for (int p = 0; p < vars.size(); p++){
			int matchVar = capsule.new_variable();
			DEBUG(capsule.registerVariable(matchVar,"match leaf " + pad_int(l) + " + position " + pad_int(p)));
			matching.matchingPerLeaf[l].push_back(matchVar);
			matching.matchingPerPosition[p].push_back(matchVar);
			if (leafSOG->leafContainsEffectAction[l]){
				matching.matchingPerPositionAMO[p].push_back(matchVar);
			} else{
				cout << "Don't include " << l << "@" <<p << endl
				DEBUG(cout << "Don't include " << l << "@" <<p << endl);
			}
		}
	}

	ipasir_init_reals(solver, leafSOG->numberOfVertices, vars.size());

	ipasir_init_leaf_tasks(solver, leafSOG->numberOfVertices);//, htn->numActions, leafSOG);

	for(int l = 0; l < leafSOG->numberOfVertices; l++){
		ipasir_init_leaf_task(solver, l, leafSOG->leafOfNode[l]);
	}

	ipasir_init_position_tasks(solver, leafSOG->numberOfVertices, vars.size());


	vector<int> leafActive (leafSOG->numberOfVertices);
	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		int activeVar = capsule.new_variable();
		DEBUG(capsule.registerVariable(activeVar,"active leaf " + pad_int(l)));
		leafActive[l] = activeVar;
	}

	vector<int> positionActive (vars.size());
	for (int p = 0; p < vars.size(); p++){
		int activeVar = capsule.new_variable();
		DEBUG(capsule.registerVariable(activeVar,"active position " + pad_int(p)));
		positionActive[p] = activeVar;
	}

	////////////////////////////// constraints that

	/*Term zero = s->mkInteger(0);
	Term nVertices = s->mkInteger(leafSOG->numberOfVertices);
	Term nPositions = s->mkInteger(vars.size());

	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		Term constraint = s->mkTerm(cvc5::Kind::LT, {rleafs[l], nPositions});
		s->assertFormula(constraint);
	}


	for (int p = 0; p < vars.size(); p++){
		Term constraint = s->mkTerm(cvc5::Kind::LT, {rpositions[p], nVertices});
		s->assertFormula(constraint);
	}

	// bad method
	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		Term nl = s->mkInteger(l);
		for (int p = 0; p < vars.size(); p++){
			Term np = s->mkInteger(p);
			Term constraint1 = s->mkTerm(cvc5::Kind::EQUAL, {rleafs[l], np});
			Term constraint2 = s->mkTerm(cvc5::Kind::EQUAL, {rpositions[p], nl});
			Term constraint3 = s->mkTerm(cvc5::Kind::EQUAL, {constraint1, constraint2});
			s->assertFormula(constraint3);

		}
	}

	Term constraint = s->mkTerm(cvc5::Kind::DISTINCT, rleafs);
	s->assertFormula(constraint);*/

	// if leaf l @ position p, then any successor of l is forbidden at p-1
	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		for (int lSucc : leafSOG->successorSet[l]){
			if(lSucc != l)
				ipasir_reals_successor(solver, l, lSucc);
		}
	}

	// AMO one position per path
//	for (int l = 0; l < leafSOG->numberOfVertices; l++)
//		atMostOne(solver,capsule,matching.matchingPerLeaf[l]);

	// AMO paths per position
	// but only consider paths that can actually contain an action with an effect
//	for (int p = 0; p < vars.size(); p++)
//		atMostOne(solver,capsule,matching.matchingPerPositionAMO[p]);


	// activity of leafs
	for (int l = 0; l < leafSOG->numberOfVertices; l++){

		PDT * leaf = leafSOG->leafOfNode[l];
		vector<int> leafVariables;
		for (int prim = 0; prim < leaf->possiblePrimitives.size(); prim++){
			if (leaf->primitiveVariable[prim] == -1) continue; // pruned

			leafVariables.push_back(leaf->primitiveVariable[prim]);
		}

//		impliesOr(solver,leafActive[l],leafVariables);
//		notImpliesAllNot(solver,leafActive[l],leafVariables);

		ipasir_reals_active(solver, l, leafActive[l]);
	}


	// if path is active one of its matchings must be true

	//for (int l = 0; l < leafSOG->numberOfVertices; l++)
	//	impliesOr(solver,leafActive[l],matching.matchingPerLeaf[l]);


	// actions at positions must be caused
	for (int p = 0; p < vars.size(); p++){
		vector<int> positionVariables;
		for (auto [pvar,prim] : vars[p])
			if (htn->numAdds[prim] != 0 || htn->numDels[prim] != 0)
				positionVariables.push_back(pvar);

//		impliesOr(solver,positionActive[p],positionVariables);
//		notImpliesAllNot(solver,positionActive[p],positionVariables);
	}

	// if position is active one of its matchings must be true
//	for (int p = 0; p < vars.size(); p++)
//		impliesOr(solver,positionActive[p],matching.matchingPerPositionAMO[p]);




	for (int p = 0; p < vars.size(); p++){
		// variable data structure
		vector<int> variablesPerPrimitive(htn->numActions);

		for (auto & [pvar,prim] : vars[p]){
			variablesPerPrimitive[prim] = pvar;
		}

		// go through all leafs
		for (int l = 0; l < leafSOG->numberOfVertices; l++){
			PDT * leaf = leafSOG->leafOfNode[l];

			if (leafSOG->firstPossible[l] > p || leafSOG->lastPossible[l] < p){

				// potentially need to implement this one
			//	assertNot(solver,matching.matchingPerPosition[p][l]);
				continue;
			}

			for (int primC = 0; primC < leaf->possiblePrimitives.size(); primC++){
				cout << "\nl";
				cout << l;
				cout << "p";
				cout << p;
				cout << "poss";
				cout << leaf->possiblePrimitives[primC];
				cout << "pv";
				cout << leaf->primitiveVariable[primC];
				if (leaf->primitiveVariable[primC] == -1) continue; // pruned
				int prim = leaf->possiblePrimitives[primC];

				// if this leaf is connected then the task must be present

			//	impliesAnd(solver,matching.matchingPerPosition[p][l],leaf->primitiveVariable[primC],variablesPerPrimitive[prim]);
			//	ipasir_reals_contained(solver, p, l, leaf->primitiveVariable[primC],variablesPerPrimitive[prim]);
			}
			cout << "|";
			cout << leafSOG->firstPossible[l];
			cout << "|";
			cout << leafSOG->lastPossible[l];
		}
	}


	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		if (!leafSOG->leafContainsEffectAction[l]) continue;
		// determine the possible primitives for this leaf
		vector<int> leafPrimitives (htn->numActions);
		PDT * leaf = leafSOG->leafOfNode[l];
		for (int primC = 0; primC < leaf->possiblePrimitives.size(); primC++){
			leafPrimitives[leaf->possiblePrimitives[primC]] = leaf->primitiveVariable[primC];
		}

		for (int p = 0; p < vars.size(); p++)
			for (auto [pvar,prim] : vars[p]){
				if (htn->numAdds[prim] != 0 || htn->numDels[prim] != 0){
				if (leafPrimitives[prim] > 0){
					// the leaf can potentially contain the action
			//			impliesAnd(solver,matching.matchingPerPosition[p][l],pvar,leafPrimitives[prim]);
				} else {
					// this is implicitly a bi-implication
			//		impliesNot(solver,matching.matchingPerPosition[p][l],pvar);
				}
				}
			}
	}

	for (int p = 0; p < vars.size(); p++){
		for (auto [pvar,prim] : vars[p]){
			ipasir_constrain_task_positions(solver, prim, p, pvar);
		}
	}
/*
	////////////////////////// impose the encoded order
	vector<vector<int>> forbiddenPerLeaf (leafSOG->numberOfVertices);
	vector<vector<int>> forbiddenPerPosition (vars.size());

	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		for (int p = 0; p < vars.size(); p++){
			int forbiddenVar = capsule.new_variable();
			DEBUG(capsule.registerVariable(forbiddenVar,"forbidden leaf " + pad_int(l) + " + position " + pad_int(p)));
			forbiddenPerLeaf[l].push_back(forbiddenVar);
			forbiddenPerPosition[p].push_back(forbiddenVar);
		}
	}


	// if leaf l @ position p, then any successor of l is forbidden at p-1
	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		for (int lSucc : leafSOG->adj[l]){
			for (int p = 1; p < vars.size(); p++){
				implies(solver,matching.matchingPerLeaf[l][p],forbiddenPerLeaf[lSucc][p-1]);
			}
		}
	}

	// forbidden-ness gets implied onwards
	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		for (int lSucc : leafSOG->adj[l]){
			for (int p = 0; p < vars.size(); p++){
				implies(solver, forbiddenPerLeaf[l][p], forbiddenPerLeaf[lSucc][p]);
			}
		}
	}

	// forbidden-ness gets implied on the positions
	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		for (int p = 1; p < vars.size(); p++){
			implies(solver, forbiddenPerLeaf[l][p], forbiddenPerLeaf[l][p-1]);
		}
	}


	// forbidden-ness forbids matchings
	for (int l = 0; l < leafSOG->numberOfVertices; l++){
		for (int p = 0; p < vars.size(); p++){
			impliesNot(solver,forbiddenPerLeaf[l][p],matching.matchingPerLeaf[l][p]);
		}
	}
*/

	return;



	cout << "Hallo!" << endl;
}
