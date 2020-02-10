#ifndef SYN_NNF_H
#define SYN_NNF_H

#include "MainSolver.h"
#include <vector>
#include <set>
#include "Basics.h"
#include "DecisionTree.h"
#include "InstanceGraph/InstanceGraph.h"

class synSolver: public CMainSolver
{
    vector <int> varsX;
    vector <int> varsY;
    vector <bool> tseitinClauses;
    vector <vector<int> > allClauses;
    vector <vector<int> > workingClauses;

    vector <int> onlyXClauses; // They do not take part in the decomposition to begin with. Need to be added later on.
    set <int> activeY;
    int tseitinVars;

public:
    synSolver();
//bool createfromPrep( vector<vector<int> > &clauses, unsigned int nVars, vector<int>& varsY, set<int>& actY);
    void init ( );
    void CreateSynNNF(vector<vector<int> > &clauses, vector<int>& Xvar, vector<int>& Yvar, vector<bool>& TseitinClauses);
    bool recordRemainingComps() override;//made virtual for c2syn - SS
    bool findVSADSDecVar(LiteralIdT &theLit, const CComponentId & superComp) override;
	bool getComp(const VarIdT &theVar, const CComponentId &superComp,
			viewStateT lookUpCls[], viewStateT lookUpVars[]) override; //made virtual for c2syn - SS

	bool decide() override;
    void getCompInputsAndTseitin(const CComponentId &superComp, viewStateT lookUpCls[], viewStateT lookUpVars[]);
    bool OnlyX (const CComponentId & superComp);
//   unsigned int makeVariable(unsigned int VarNum);
    bool createfromPrep( vector<vector<int> > &clauses, unsigned int nVars); // vector<int> &varsY)
};
#endif
