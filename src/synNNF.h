#ifndef SYN_NNF_H
#define SYN_NNF_H

#include "MainSolver.h"
#include <vector>
#include <set>
#include <map>
#include <assert.h>
#include "Basics.h"
#include "DecisionTree.h"
#include "InstanceGraph/InstanceGraph.h"

class synSolver: public CMainSolver
{
    vector <int> varsX;
    vector <int> varsY;
    vector <bool> tseitinClauses;
    vector <int> tseitinVars;
    vector <vector<int> > allClauses;
    vector <vector<int> > workingClauses;
    vector<bool> activeY;
    vector<bool> tseitinY;

    vector <int> onlyXClauses; // They do not take part in the decomposition to begin with. Need to be added later on.
    set <int> activeYVars;
//    int tseitinVars;

public:
    synSolver();
//bool createfromPrep( vector<vector<int> > &clauses, unsigned int nVars, vector<int>& varsY, set<int>& actY);
    void init ( );
    void CreateSynNNF(vector<vector<int> > &clauses, vector<int>& Xvar, vector<int>& Yvar, vector<bool>& TseitinClauses, vector<int>&);
    bool recordRemainingComps() override;//made virtual for c2syn - SS
    bool findVSADSDecVar(LiteralIdT &theLit, const CComponentId & superComp) override;
	bool getComp(const VarIdT &theVar, const CComponentId &superComp,
			viewStateT lookUpCls[], viewStateT lookUpVars[]) override; //made virtual for c2syn - SS

	bool decide() override;
 //   void getCompInputsAndTseitin(const CComponentId &superComp, viewStateT lookUpCls[], viewStateT lookUpVars[]);
    bool OnlyX (const CComponentId & superComp);
//    unsigned int makeVariable(unsigned int VarNum);
    bool createfromPrep( vector<vector<int> > &clauses, unsigned int nVars); // vector<int> &varsY)
    void attachComponent ();
	string writeDTree(ofstream& ofs) ;
    void writeDSharp_rec(DTNode* node, ofstream& ofs, map<int, string> & visited) ;
    void writeOPtoBLIF_rec(vector<string> &children, bool isOR, ofstream& ofs, string out) ;
    void printSynNNF();

private:
	string getInputName(int var) ;
	string getInputNegName(int var) ;
	void instantiateOnOff(ofstream & ofs) ;
	string getIDName(int id) ;
	void    writeOFF(ofstream& ofs);
    void    writeON(ofstream& ofs);
    void	writeOR(ofstream& ofs);
    void	writeAND(ofstream& ofs);
    void	writeEqual(ofstream& ofs);
    void	writeNEG(ofstream& ofs);
    void	writeXOR(ofstream& ofs);
};
#endif
