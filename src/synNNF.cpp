#include "synNNF.h"


synSolver::synSolver()
{
    varsX.clear();
    varsY.clear();
    tseitinVars.clear();

}

void synSolver::init()
{
    int Y;
    bool containsActY = false;
    cout << " Size of all Clauses " << allClauses.size() << endl;

    int numVars = varsX.size() + varsY.size();
    activeY.resize(numVars+1, 0); //All vars not active to begin with
    tseitinY.resize(numVars+1, 0); //All vars not tseitin to begin with

    for (auto &it: tseitinVars)
        tseitinY[it] = true; //Assigning true to TseitinVars

    for (auto &it : varsY)
    {
        if (! tseitinY[it])
        {
            activeY[it] = true;
            this->priorityVars.insert(it);
        }
    }

    for (int i = 1; i < numVars+1; i++)
    {
        cout << i <<  ": Tseitin Var "  << tseitinY[i] << " Active Var : " << " "  << activeY[i] << endl;
    }

    cout << "priorityVars " << endl;
    for (auto &it : this->priorityVars)
        cout << it << " " ;
    cout << endl;
    //print priorityVars
    for (int i = 0; i < allClauses.size(); i++)
    {
                //if (tseitinClauses[i])  //Ignore the clause as it is a tseitin clause
                 //   continue;   
                containsActY = false;  

                cout << " Clause " << i ;

                for (int j = 0; j < allClauses[i].size(); j++)
                {
                    Y = abs (allClauses[i][j]);               
                    
                    cout << " " << allClauses[i][j] ;
                    if (activeY[Y] || tseitinY[Y])
                        containsActY = true;
                }
                cout << endl ;
                if (containsActY)
                    workingClauses.push_back(allClauses[i]);
               else
               {
                    onlyXClauses.push_back(allClauses[i]);
                    cout << "Clause" << i << "contains only X vars " << endl;
               }

                cout << " Size of workingClauses " << workingClauses.size() << endl;

    }
    //cout << " ActiveY "  ;
    //for (auto &it: activeYVars)
     //        cout << it << " " ;
    //cout << endl;
}

void synSolver::CreateSynNNF(vector<vector<int> > &cls, vector<int>& Xvar, vector<int>& Yvar, vector<bool>& TseitinCls, vector<int> & tVars, string fileName, set <int> & dc, map<int, vector<int> > & da, map<int, vector<int> > & dor, map<int, vector<int> > & dx)
{
        cout << " In CreateSynNNF" << endl;
        allClauses = cls;
        varsX = Xvar;
        varsY = Yvar; 
        tseitinVars = tVars;
        tseitinClauses = TseitinCls; //set<int> actY; 
        baseFileName = fileName;
        depCONST = dc;
        depAND = da;
        depOR = dor;
        depXOR = dx;
        cout << "X: " ;
        for (int j = 0; j < Xvar.size(); j++)
             cout << Xvar[j] << " " ;
        cout << endl;
        cout << "Y: " ;
        for (int j = 0; j < Yvar.size(); j++)
                 cout << Yvar[j] << " " ;
        cout << endl;
            init ();
            cout << " Init done. Calling createfromPrep " << endl;

            createfromPrep( workingClauses, Xvar.size() + Yvar.size()); //Create the data structures;
              cout << " Size of workingClauses " << workingClauses.size() << endl;
            
            cout << "Size of actY " << activeYVars.size() << endl;

            solve (NULL);
            printSynNNF();

}

/** Changing the code to only create components for Y vars **/
/** Code copied from src_sharpSAT/MainSolver/MainSolver.cpp **/

bool synSolver::decide()
{
	LiteralIdT theLit(NOT_A_LIT);

	CStepTime::stepTime(); // Solver-Zeit


	if (CStepTime::getTime() - xFormulaCache.getLastDivTime()
			> xFormulaCache.getScoresDivTime())
	{
		xFormulaCache.divCacheScores();
		xFormulaCache.setLastDivTime(CStepTime::getTime());
	}

	if (!bcpImplQueue.empty())
		return true;

	if (!decStack.TOS_hasAnyRemComp())
	{
		recordRemainingComps();
        cout << "Num. of remaining comps " << (unsigned int) decStack.TOS_countRemComps() << endl;
		if (decStack.TOS_countRemComps() == 0)
		{
			handleSolution();
			return false;
		}
	}

        
	if (!findVSADSDecVar(theLit, decStack.TOS_NextComp())
			|| decStack.TOS_NextComp().getClauseCount() == 0) // i.e. component satisfied
	{
        if (decStack.TOS_NextComp().getClauseCount () == 0)
            cout << "Next Comp has no clauses " << endl;
        else
        {
            cout << " findVSADDecVar returned false. " << endl;

            if (OnlyX(decStack.TOS_NextComp()))
            {
                attachComponent();
                handleSolution();
                decStack.TOS_popRemComp();
                return true;
            }
        }
       // attachComponent();
	    handleSolution();
		decStack.TOS_popRemComp();
		return false;
	}

	//checkCachedCompVal:
	static CRealNum cacheVal;

	//decStack.TOS_NextComp();

	if (CSolverConf::allowComponentCaching && xFormulaCache.extract(
			decStack.TOS_NextComp(), cacheVal,
			decStack.top().getCurrentDTNode()))
	{
		decStack.top().includeSol(cacheVal);
		theRunAn.addValue(SOLUTION, decStack.getDL());
		decStack.TOS_popRemComp();
		return false;
	}
	/////////////////////////////

	// Create the nodes
    cout << "Deciding "  << theLit.toSignedInt() << endl;
	DTNode * newNode = new DTNode(DT_OR, num_Nodes++);
	DTNode * left = new DTNode(DT_AND, num_Nodes++);
	DTNode * right = new DTNode(DT_AND, num_Nodes++);
	DTNode * leftLit = get_lit_node(theLit.toSignedInt());
	DTNode * rightLit = get_lit_node(-1 * theLit.toSignedInt());

	newNode->choiceVar = theLit.toSignedInt();

	// Set the parents
	left->addParent(newNode, true);
	leftLit->addParent(left, true);
	right->addParent(newNode, true);
	rightLit->addParent(right, true);
	newNode->addParent(decStack.top().getCurrentDTNode(), true);

	decStack.push(newNode);
	bcpImplQueue.clear();
	bcpImplQueue.push_back(AntAndLit(NOT_A_CLAUSE, theLit));

	theRunAn.addValue(DECISION, decStack.getDL());

	if (theRunAn.getData().nDecisions % 255 == 0)
	{
		doVSIDSScoreDiv();
	}

    cout << "Printing Decision Tree with " << theLit.toSignedInt() << endl;
    decStack.top().getCurrentDTNode()->print(); 
	return true;
}
void synSolver::attachComponent()
{
    
	LiteralIdT theLit(NOT_A_LIT);
    vector <LiteralIdT> allLits;
  //  if (OnlyX(decStack.TOS_NextComp()))
   // {
        cout << " num_Nodes = " << num_Nodes << endl;
       decStack.top().getDTNode()->print();
        
        CComponentId & refSupComp = decStack.TOSRefComp();
        cout << "In attach Component. RefsupComp " << refSupComp.id << endl;
        if (refSupComp.countCls() > 1)
        {
            DTNode * newNode = new DTNode(DT_AND, num_Nodes++);
            //add the literals corresponding to the clauses containing Xvar


            vector<ClauseIdT>::const_iterator itCl;
            vector<VarIdT>::const_iterator itV;
            int numVar = 0;
            int totVar = 0;
            for (itCl = refSupComp.clsBegin(); *itCl != clsSENTINEL; itCl++)
            {
                    LiteralIdT *prev = NULL;
                    printClause (*itCl);
                    DTNode *cl = new DTNode (DT_OR, num_Nodes++);
                    numVar = 0;
                    
                    for (vector<LiteralIdT>::iterator itX = begin(getClause(*itCl)); *itX != ClauseEnd(); itX++)
                    {
                        LiteralIdT curr = *itX;
                        allLits.push_back(curr);
                        if (getVar(*itX).isActive  ())
                        {
                            cout << "Lit " << curr.toSignedInt() << " " ;
                            numVar ++;
                            if (prev == NULL)
                                prev = & *itX;
                            else
                            {
                                DTNode *litNode = get_lit_node (curr.toSignedInt());
                                litNode->addParent(cl, true);
	                            bcpImplQueue.push_back(AntAndLit(NOT_A_CLAUSE, curr));
                                
                             }
                        }
                        if (prev != NULL)
                        {
                            DTNode *prevNode = get_lit_node (prev->toSignedInt());
                            if (numVar > 1)
                            {
                                   cl->addParent(newNode, true);
                                   prevNode->addParent(cl, true);
                                   cout << "Printing new clauses " <<endl;
                                   cl->print();
                                   cout << endl;
                            } 
                            else
                            {
                                   prevNode->addParent(newNode, true);
                                   prevNode->print();
                                   cout << endl;
                                   cout << "Printing prev node" << endl;
	                                bcpImplQueue.push_back(AntAndLit(NOT_A_CLAUSE, *prev));
                            }
                        }
                        totVar+= numVar;

                    }
            }
         //   printTree();
         if (totVar > 0)
         {
            newNode->addParent(decStack.top().getCurrentDTNode(), true);
                                   cout << "Printing comp tree  " <<endl;
           newNode->print();
           cout << endl;
            decStack.push(newNode);
         }
          //  decStack.top().getDTNode()->print();

	        /*CVariableVertex  pVar;
            for ( itV = refSupComp.varsBegin(); *itV != varsSENTINEL; itV++)
            {
                
                pVar = getVar(*itV);
                if (tseitinY[pVar.getVarNum()])
                {
                    pVar.setVal (true, decStack.getDL(), 0);
                    cout << "Setting pVar " << pVar.getVarNum() << " to true" << endl;
                }
                   
            }
            */

        }
        else
            cout << "Empty Component " << endl;
    //}

//Assigning Tseitin vars as True temporarily.

}
bool synSolver::recordRemainingComps()
{
    cout << " In recordRemainingComps in synSolver " << endl;
	CComponentId & refSupComp = decStack.TOSRefComp();

	viewStateT lookUpCls[getMaxOriginalClIdx() + 2];
	viewStateT lookUpVars[countAllVars() + 2];

	memset(lookUpCls, NIL, sizeof(viewStateT) * (getMaxOriginalClIdx() + 2));
	memset(lookUpVars, NIL, sizeof(viewStateT) * (countAllVars() + 2));

	vector<VarIdT>::const_iterator vt;
	vector<ClauseIdT>::const_iterator itCl;

    cout << "RefSupComp "  << refSupComp.id << endl;
   // printComponent(refSupComp);
    //cout << endl;

	for (itCl = refSupComp.clsBegin(); *itCl != clsSENTINEL; itCl++)
	{
		lookUpCls[*itCl] = IN_SUP_COMP;
	}

    bool containsActive = false;
	for (vt = refSupComp.varsBegin(); *vt != varsSENTINEL; vt++)
	{
		if (getVar(*vt).isActive() )// || getVar(*vt).getVal() == T || getVar(*vt).getVal() == I)
        {
                
                lookUpVars[*vt] = IN_SUP_COMP;
                getVar(*vt).scoreDLIS[true] = 0;
                getVar(*vt).scoreDLIS[false] = 0;
         }
	}

	componentSearchStack.clear();
	
    for (vt = refSupComp.varsBegin(); *vt != varsSENTINEL; vt++)
      {
        //What happens if only  X vars are present in refSupComp
                //cout << "In recordRemComps " << getLitIdT(true).toSignedInt()*vt << endl;
                //cout << "in RRC: var " << *vt << " lit: " << getVar(*vt).getLitIdT(true).toVarIdx() << endl;
                if (lookUpVars[*vt] == IN_SUP_COMP && activeY[*vt])
                {
                    decStack.TOS_addRemComp();
                    decStack.lastComp().setTrueClauseCount(0);
                    lookUpVars[*vt] = SEEN;
                    componentSearchStack.push_back(*vt);
                //    cout << "Added " << *vt << " to comp stack" << endl;
                    getComp(*vt, decStack.TOSRefComp(), lookUpCls, lookUpVars);
                    decStack.lastComp().addVar(varsSENTINEL);
                    decStack.lastComp().addCl(clsSENTINEL);
                    cout << "new component " << decStack.lastComp().id << endl;
                    //printComponent (decStack.lastComp());
                    //cout << endl;
                }
                    
        }

	decStack.TOS_sortRemComps();
	return true;
}
/*
//Component for X and Tseitin Vars. 
void synSolver::getCompInputsAndTseitin(const CComponentId &superComp,
		viewStateT lookUpCls[], viewStateT lookUpVars[])
{
	vector<VarIdT>::const_iterator vt, itVEnd;

	vector<LiteralIdT>::const_iterator itL;
	vector<ClauseIdT>::const_iterator itCl;

	CVariableVertex * pActVar;

	unsigned int nClausesSeen = 0, nBinClsSeen = 0;

	for (vt = superComp.varsBegin(); *vt != varsSENTINEL; vt++)
    {
		pActVar = &getVar(*vt);
		//BEGIN traverse binary clauses
		for (itL = pActVar->getBinLinks(true).begin(); *itL != SENTINEL_LIT; itL++)
			if (lookUpVars[itL->toVarIdx()] == IN_SUP_COMP )
				nBinClsSeen++;

		for (itL = pActVar->getBinLinks(false).begin(); *itL != SENTINEL_LIT; itL++)
			if (lookUpVars[itL->toVarIdx()] == IN_SUP_COMP )
				nBinClsSeen++;
    }
	for (vt = superComp.varsBegin(); *vt != varsSENTINEL; vt++)
		if (lookUpVars[*vt] == IN_SUP_COMP) //we have to put a var into our component
		{
			decStack.lastComp().addVar(*vt);
			lookUpVars[*vt] = IN_OTHER_COMP;
		}

	//decStack.lastComp().addVar(varsSENTINEL); // Moved to above

	/////////////////////////////////////////////////
	// END store variables in resComp
	/////////////////////////////////////////////////

	for (itCl = superComp.clsBegin(); *itCl != clsSENTINEL; itCl++)
		if (lookUpCls[*itCl] == IN_SUP_COMP)
		{
			decStack.lastComp().addCl(*itCl);
			lookUpCls[*itCl] = IN_OTHER_COMP;
            nClausesSeen ++;
		}
	//decStack.lastComp().addCl(clsSENTINEL); // Moved to above
	
	decStack.lastComp().addTrueClauseCount(nClausesSeen + nBinClsSeen);

}
*/

bool synSolver::getComp(const VarIdT &theVar, const CComponentId &superComp,
		viewStateT lookUpCls[], viewStateT lookUpVars[])
{
    /* Moved to above */
	//componentSearchStack.clear();
	//lookUpVars[theVar] = SEEN;
	//componentSearchStack.push_back(theVar);
	
	vector<VarIdT>::const_iterator vt, itVEnd;

	vector<LiteralIdT>::const_iterator itL;
	vector<ClauseIdT>::const_iterator itCl;

	CVariableVertex * pActVar;

	unsigned int nClausesSeen = 0, nBinClsSeen = 0;

	for (vt = componentSearchStack.begin(); vt != componentSearchStack.end(); vt++)
	// the for-loop is applicable here because componentSearchStack.capacity() == countAllVars()
	{
		pActVar = &getVar(*vt);
		//BEGIN traverse binary clauses
		for (itL = pActVar->getBinLinks(true).begin(); *itL != SENTINEL_LIT; itL++)
			if (lookUpVars[itL->toVarIdx()] == IN_SUP_COMP )
			{
                //cout << "In getComp.Processing " << itL->toVarIdx() << "Unsigned Int " << itL->toUInt() << " activeY is " << activeY[itL->toVarIdx()] << " or " << activeY[itL->toUInt()] << endl;
				nBinClsSeen++;
				lookUpVars[itL->toVarIdx()] = SEEN;
                if (activeY[itL->toVarIdx()] )// || tseitinVars[itL->toVarIdx()])  //Add to the component only if output variable
                //if (activeY[itL->toVarIdx()] )  //Add to the component only if output variable
                {
				    componentSearchStack.push_back(itL->toVarIdx());
				    getVar(*itL).scoreDLIS[itL->polarity()]++;
				    pActVar->scoreDLIS[true]++;
                }
			}
		for (itL = pActVar->getBinLinks(false).begin(); *itL != SENTINEL_LIT; itL++)
			if (lookUpVars[itL->toVarIdx()] == IN_SUP_COMP)
			{
				nBinClsSeen++;
				lookUpVars[itL->toVarIdx()] = SEEN;
                if (activeY[itL->toVarIdx()] )// || tseitinVars[itL->toVarIdx()])  //Add to the component only if output variable
               // if (activeY[itL->toVarIdx()] )  //Add to the component only if output variable
                {
				    componentSearchStack.push_back(itL->toVarIdx());
                    getVar(*itL).scoreDLIS[itL->polarity()]++;
                    pActVar->scoreDLIS[false]++;
             //       cout << "Adding " << itL->toVarIdx() << "comp of " << pActVar->getVarNum() << endl;
                }
			}
		//END traverse binary clauses


		for (itCl = var_InClsBegin(*pActVar); *itCl != SENTINEL_CL; itCl++)
        {
           // cout << "lookUpClsNil = " << (lookUpCls[*itCl] == NIL) << endl;
            //cout << "lookUpClsSeen = " << (lookUpCls[*itCl] == SEEN) << endl;
            //cout << "lookUpClsSupCOmp = " << (lookUpCls[*itCl] == IN_SUP_COMP) << endl;

            if (lookUpCls[*itCl] == SEEN)
                continue;
			if (lookUpCls[*itCl] == IN_SUP_COMP)
			{
				itVEnd = componentSearchStack.end();
				for (itL = begin(getClause(*itCl)); *itL != ClauseEnd(); itL++)
					if (lookUpVars[itL->toVarIdx()] == NIL) //i.e. the var is not active
					{
                           cout << itL->toVarIdx() << " is NIL"  << endl;
						if (!isSatisfied(*itL))
                        {
                            cout << "clause " <<  (*itL).toSignedInt() << " is not satisfied " << endl;
							continue;
                        }
						//BEGIN accidentally entered a satisfied clause: undo the search process
						while (componentSearchStack.end() != itVEnd)
						{
							lookUpVars[componentSearchStack.back()]
									= IN_SUP_COMP;
							componentSearchStack.pop_back();
						}
						lookUpCls[*itCl] = NIL;
						for (vector<LiteralIdT>::iterator itX = begin(
								getClause(*itCl)); itX != itL; itX++)
						{
							if (getVar(*itX).scoreDLIS[itX->polarity()] > 0)
								getVar(*itX).scoreDLIS[itX->polarity()]--;
						}
						//END accidentally entered a satisfied clause: undo the search process
						break;

					}
					else
					{
                    //      cout << "Adding " << itL->toVarIdx() << " through clauses in comp of " << pActVar->getVarNum() << endl;
                     //     cout <<  (itL->toVarIdx() == IN_SUP_COMP) << " vAr in supcomp " << endl;

						getVar(*itL).scoreDLIS[itL->polarity()]++;
						if (lookUpVars[itL->toVarIdx()] == IN_SUP_COMP )
						{
							lookUpVars[itL->toVarIdx()] = SEEN;
                      //      cout << " Changing lookUpVars for " << itL->toVarIdx() << " to seen " << endl;
                                if (activeY[itL->toVarIdx()] )//|| tseitinVars[itL->toVarIdx()])  //Add to the component only if output variable
							    componentSearchStack.push_back(itL->toVarIdx());
						}
					}
                }
      //      cout << "PostlookUpClsNil = " << (lookUpCls[*itCl] == NIL) << endl;
       //     cout << "PostlookUpClsSeen = " << (lookUpCls[*itCl] == SEEN) << endl;
        //    cout << "PostlookUpClsSupCOmp = " << (lookUpCls[*itCl] == IN_SUP_COMP) << endl;

				if (lookUpCls[*itCl] == NIL)
					continue;
				nClausesSeen++;
				lookUpCls[*itCl] = SEEN;
			}
	}

	/////////////////////////////////////////////////
	// BEGIN store variables in resComp
	/////////////////////////////////////////////////

	decStack.lastComp().reserveSpace(componentSearchStack.size(), nClausesSeen);

	for (vt = superComp.varsBegin(); *vt != varsSENTINEL; vt++)
		if (lookUpVars[*vt] == SEEN) //we have to put a var into our component
		{
			decStack.lastComp().addVar(*vt);
			lookUpVars[*vt] = IN_OTHER_COMP;
            cout << "Adding var " << *vt << " to lastComp " << endl;
		}

	//decStack.lastComp().addVar(varsSENTINEL); // Moved to above

	/////////////////////////////////////////////////
	// END store variables in resComp
	/////////////////////////////////////////////////

	for (itCl = superComp.clsBegin(); *itCl != clsSENTINEL; itCl++)
		if (lookUpCls[*itCl] == SEEN)
		{
			decStack.lastComp().addCl(*itCl);
			lookUpCls[*itCl] = IN_OTHER_COMP;
            //cout << "Adding clause " << *itCl << " to lastComp " << endl;
		}
	//decStack.lastComp().addCl(clsSENTINEL); // Moved to above
	
	decStack.lastComp().addTrueClauseCount(nClausesSeen + nBinClsSeen);

    cout <<" Added new component to decStack " << endl;
   if (nClausesSeen == 0)
       cout << " No clauses added to the component. nClausesSeen == 0. " << endl;
   //else
   //{
    //   cout<< "New Component" << endl;
     //  printComponent(decStack.lastComp());
      // cout << endl;
   //}

	return true;
}

bool synSolver::findVSADSDecVar(LiteralIdT &theLit, const CComponentId & superComp)
{
    cout << "In findVSADSDecVar in SynSolver" << endl;

	vector<VarIdT>::const_iterator it;

	int score = -1;
	int pr_score = -1;
	int bo;
	PVARV pVV = NULL;
	PVARV pr_pVV = NULL;

	for (it = superComp.varsBegin(); *it != varsSENTINEL; it++)
    {
		if (getVar(*it).isActive()  && activeY[*it]) //decide only on output vars (tseitinVars are excluded from this
		{
     //   cout << " Considering variable " << getVar(*it).getVarNum()<< ". Lit id: (T) " << getVar(*it).getLitIdT(true).toSignedInt() << ". Lit id: (F):" << getVar(*it).getLitIdT(false).toSignedInt() << endl;
      //  cout << (*it) << " Var Num " << getVar(*it).getVarNum() << endl;
			bo = (int) getVar(*it).getVSIDSScore() + getVar(*it).getDLCSScore();

			if (bo > score)
			{
				score = bo;
				pVV = &getVar(*it);
			}
            //cout << " bo: is " << bo << endl;
			
			if (0 != priorityVars.count(*it))
			{
                cout << " Is a priority Var " << endl;
			    if (bo > pr_score)
			    {
				    pr_score = bo;
				    pr_pVV = &getVar(*it);
			    }
			}
		}
    }	
	// If we have a priority variable remaining, then take the best one as a decision
	if (-1 != pr_score) {
	    score = pr_score;
	    pVV = pr_pVV;
	}

	if (pVV == NULL || pr_score == -1 ) //We want to branch only on Y variables... 
		return false;

	bool pol = pVV->scoreDLIS[true] + pVV->scoreVSIDS[true]
			> pVV->scoreDLIS[false] + pVV->scoreVSIDS[false];

	theLit = pVV->getLitIdT(pol);

	return true;
}
//Return true if it contains only X and Tseitin Vars. We cannot decide on these and hence just attach the component.
bool synSolver::OnlyX (const CComponentId & superComp)
{
	    vector<VarIdT>::const_iterator it;
        int numVar = 0;
	    for (it = superComp.varsBegin(); *it != varsSENTINEL; it++)
        {
            numVar++;
		    if (getVar(*it).isActive())
            {
                if ( activeY[(*it)] ) //|| tseitinVars[*it])
                    return false;
            }
         }
         return (numVar > 0);
        // return true;
}

 /* Added by Shetal - to create directly from the preprocessed data 
    Modified createfromFile to create from pre-read clauses by readCnf */
bool synSolver::createfromPrep( vector<vector<int> > &clauses, unsigned int nVars) // vector<int> &varsY)
{
	//unsigned int nVars= Xvar.size() + Yvar.size();
    unsigned int nCls=clauses.size();

	vector<int> litVec;
	vector<TriValue> seenV;
	int clauseLen = 0;
	TriValue pol;

	vector<int> varPosMap;

	// BEGIN INIT
	reset(); // clear everything
	// END INIT

	///BEGIN File input
	originalVarCount = nVars;

	vector<int>::iterator it, jt;

	int actVar;
	
	int ilitA, ilitB, lengthCl;
	LiteralIdT LitA, LitB;
	ClauseIdT idCl;

	seenV.resize(nVars + 1, X);
	varPosMap.resize(nVars + 1, -1);
	theVars.reserve(nVars + 1);
	theLitVector.reserve(litVec.size());
	theClauses.reserve(nCls + 10000);

	varTranslation.reserve(nVars + 1);
	varUntranslation.reserve(nVars + 1);
	origTranslation.reserve(nVars + 1);

	theRunAn.init(nVars, nCls);

	vector<vector<ClauseIdT> > _inClLinks[2];

	_inClLinks[0].resize(nVars + 1);
	_inClLinks[1].resize(nVars + 1);

    for (int i = 0; i < clauses.size(); i++)
    {
	    it = clauses[i].begin();

      //  cout << "Processing clause " << i << endl;
      //  while (it != clauses[i].end())
       // {
       //     cout << *it << endl;

            jt = it;
            ilitA = 0;
            ilitB = 0; // we pick two literals from each clause for watch- or bin-creation
            lengthCl = 0;
            while (jt != clauses[i].end()) // jt passes through the clause to determine if it is valid
            {
                actVar = abs(*jt);
                
                if (seenV[actVar] == X) // literal not seen
                {
                    seenV[actVar] = (*jt > 0) ? W : F;
                    if (ilitA == 0)
                        ilitA = *jt;
                    else if (ilitB == 0)
                        ilitB = *jt;
                    jt++;
                }
            }

            lengthCl = clauses[i].size(); 

    #ifdef DEBUG
            if (ilitA == 0)
            {
                 toERROUT("ERR");
                 exit(3);
            }
    #endif

//read the clause

            actVar = abs(ilitA);
            if (varPosMap[actVar] == -1) // create new Var if not present yet
                  varPosMap[actVar] = makeVariable(actVar);

//             if (std::find (varsY.begin(), varsY.end(), actVar) != varsY.end()) //Is an output variable

            LitA = LiteralIdT(varPosMap[actVar], (ilitA > 0) ? W : F); //W stands for True (or Wahr in German). F for false (falsch) 

            if (ilitB != 0)// determine LiteralIdT for ilitB
            {
                actVar = abs(ilitB);
                if (varPosMap[actVar] == -1) // create new Var if not present yet
                    varPosMap[actVar] = makeVariable(actVar);

                LitB = LiteralIdT(varPosMap[actVar], (ilitB > 0) ? W : F);
                //if (std::find (varsY.begin(), varsY.end(), actVar) != varsY.end()) //Is an output variable
                 //   actY.insert(actVar);
            }

            if (lengthCl == 1)
                    theUnitClauses.push_back(LitA);
            else if (lengthCl == 2)
            {
    #ifdef DEBUG
                    if (ilitB == 0)
                    {
                        toERROUT("ERR BIN CL");
                        exit(3);
                    }
    #endif

                    if (!getVar(LitA).hasBinLinkTo(LitB, LitA.polarity()))
                    {
                        getVar(LitA).addBinLink(LitA.polarity(), LitB);
                        getVar(LitB).addBinLink(LitB.polarity(), LitA);
                        numBinClauses++;
                        //Binary Clauses not made!! - SS
                    }
                }
                else
                {
    #ifdef DEBUG
                    if (ilitB == 0)
                    {
                        toERROUT("ERR CL");
                        exit(3);
                    }
    #endif
                    idCl = makeClause();
                    getClause(idCl).setLitOfs(theLitVector.size());

                    theLitVector.push_back(LitA);

                    /// new
                    _inClLinks[LitA.polarity()][LitA.toVarIdx()].push_back(idCl);
                    getVar(LitA).scoreDLIS[LitA.polarity()]++;
                    ///
                    theLitVector.push_back(LitB);

                    /// new
                    _inClLinks[LitB.polarity()][LitB.toVarIdx()].push_back(idCl);
                    getVar(LitB).scoreDLIS[LitB.polarity()]++;
                    ///

                    for (jt = it + 2; jt != clauses[i].end(); jt++)
                        if (*jt != ilitB) // add all nonzero literals
                        {
                            actVar = abs(*jt);
                            pol = (*jt > 0) ? W : F;
                            if (varPosMap[actVar] == -1) // create new Var
                                varPosMap[actVar] = makeVariable(actVar);

                        
                        //    if (std::find (varsY.begin(), varsY.end(), actVar) != varsY.end()) //Is an output variable
                         //       actY.insert(actVar);
                            // add lit to litvector
                            theLitVector.push_back(LiteralIdT(varPosMap[actVar],
                                    pol));
                            /// new
                            _inClLinks[pol][varPosMap[actVar]].push_back(idCl);
                            getVar(varPosMap[actVar]).scoreDLIS[pol]++;
                            ///
                        }
                    // make an end: SENTINEL_LIT
                    theLitVector.push_back(SENTINEL_LIT);

                    getClause(idCl).setLitA(LitA);
                    getClause(idCl).setLitB(LitB);
                    getClause(idCl).setLength(lengthCl);

                    getVar(LitA).addWatchClause(idCl, LitA.polarity());
                    getVar(LitB).addWatchClause(idCl, LitB.polarity());
                }
               // it++;
            //}

            // undo the entries in seenV
            for (jt = it; jt != clauses[i].end(); jt++)
                seenV[abs(*jt)] = X;

    }

    cout << " Intitializing the INcls Vector " << endl;
	//BEGIN initialize theInClsVector
	theInClsVector.clear();
	theInClsVector.reserve(theLitVector.size() + nVars);
	theInClsVector.push_back(SENTINEL_CL);
	vector<ClauseIdT>::iterator clt;
	for (unsigned int i = 0; i <= nVars; i++)
	{
		getVar(i).setInClsVecOfs(false, theInClsVector.size());
		for (clt = _inClLinks[0][i].begin(); clt != _inClLinks[0][i].end(); clt++)
		{
			theInClsVector.push_back(*clt);
		}

		getVar(i).setInClsVecOfs(true, theInClsVector.size());
		for (clt = _inClLinks[1][i].begin(); clt != _inClLinks[1][i].end(); clt++)
		{
			theInClsVector.push_back(*clt);
		}
		theInClsVector.push_back(SENTINEL_CL);
	}
	//END initialize theInClsVector

#ifdef DEBUG
	assert(theInClsVector.size() <= theLitVector.size() + nVars + 1);
	toDEBUGOUT("inCls sz:"<<theInClsVector.size()*sizeof(ClauseIdT)<<" "<<endl);
	toDEBUGOUT("lsz: "<< theLitVector.size()*sizeof(unsigned int)<< " bytes"<<endl);
#endif

	theUClLookUp.resize(theVars.size() + 1, X);
	iOfsBeginConflictClauses = theClauses.size();

	theRunAn.setUsedVars(countAllVars());

	// Store the original translation
	origTranslation.clear();
	origTranslation.resize(varPosMap.size(), -1);
	for (int i = 0; i < varPosMap.size(); i++)
	{
		if (-1 != varPosMap[i])
			origTranslation[varPosMap[i]] = i;
	}

	//----- This is a good place to set up the var(Un)Translation
	//--- Clear it out
	varTranslation.clear();
	varUntranslation.clear();

	varTranslation.resize(nVars + 1);
	varUntranslation.resize(nVars + 1);

	//--- Put in the initial 0 (since variables start at 1)
	//---  and add the default values for all variables
	for (unsigned int i = 0; i <= countAllVars(); i++)
	{
		varTranslation[(int) i] = (int) i;
		varUntranslation[(int) i] = (int) i;
	}

	return true;
}
/**unsigned int synSolver::makeVariable(unsigned int VarNum)
{
		theVars.push_back(CVariableVertex(VarNum, theVars.size()));
        cout << "For " << VarNum << " tseitinVars " << tseitinVars[VarNum] << " activeY " << activeY[VarNum] << endl;
        if (tseitinY[VarNum])
             theVars.back().setValT() ;
        else if (!activeY[VarNum])
             theVars.back().setValI(); 

        cout << VarNum << "theVal set to " << theVars.back().getVal() << endl;
		return theVars.back().getVarIdT();

}
*/

//Taken from jatin and divya's code
void synSolver::writeComp(ofstream& ofs) {
		ofs<<".model Comp"<<endl;
		ofs<<".inputs ";

		map<string, string> inputsToDS;
		
		for(int i=1; i<=originalVarCount; i++) {
            if (activeY[i] || tseitinY[i])  //Add to the component only if output variable
            {
				string posStr = "C_OUT_"+to_string(i);
				string negStr = "C_OUT_NEG_"+to_string(i);

				ofs<<posStr<<" ";
				// ofs<<negStr<<" ";
				inputsToDS[getInputName(i)] = posStr;
				inputsToDS[getInputName(i+originalVarCount)] = negStr;
			}
			else {
				string st = "C_INP_"+to_string(i); 
				ofs<<st<<" ";
				inputsToDS[getInputName(i)] = st;
			}
		}
		ofs<<endl;
		ofs<<".outputs FHAT"<<endl;
		ofs<<".subckt DS ";
		for(auto q: inputsToDS) {
			ofs<<q.first<<"="<<q.second<<" ";
		}

		DTNode* root;
		if (1 == decStack.top().getDTNode()->numChildren())
			root = decStack.top().getDTNode()->onlyChild();
		else
			root = decStack.top().getDTNode();

		ofs<<getIDName(root->getID())<<"=FHAT"<<endl;

		ofs<<".end"<<endl;
	}

//Gives a map of Y variables in the subtree rooted at the Tseitins
void synSolver::processTseitins (vector < set<int>> & leaves)
{
	vector<set<int> > graph(originalVarCount+1);

	// Create Graph
	for(auto it: depCONST) {
		int var = abs(it);
		graph[var].insert(0);
	}
	for(auto&it: depAND) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}
	for(auto&it: depOR) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}
	for(auto&it: depXOR) {
		int var = abs(it.first);
		for(auto&it2:it.second)
			graph[var].insert(abs(it2));
	}

    bool visited[originalVarCount +1] = {false};
	for (int i = 1; i < originalVarCount + 1; ++i) {
        if (graph[i].size() > 0 )
            DFS_collectLeaves(graph, i, leaves, visited);
	}
}
    
//For now collecting all leaves... can restrict it to only activeY if needed.
void synSolver::DFS_collectLeaves(vector<set<int> >& graph, int node, vector <set <int> >& leaves, bool visited[])
{
    //if (node == 0)
     //   return;
    if (visited[node])
        return;
    
    set<int> curr_leaves;
    if (graph[node].size () <= 0) //This is a leaf?
    {
        cout << "Leaf Node " <<  node << endl;
        
        curr_leaves.insert(node);
        leaves[node] = curr_leaves; //return itself
        visited[node] = true;
        return;
    }
	for(auto &it:graph[node])
    {
        if (!visited[it]) 
            DFS_collectLeaves(graph, it, leaves, visited);

        for (auto &l: leaves[it])
        {
            if (activeY[it])
                curr_leaves.insert(l);
            cout << "Added " << l << " to leaves " << " of " << node << endl;
        }
    } 
    leaves[node] = curr_leaves;

    visited [node] = true;
    return;
}



void synSolver::printSynNNF ()
{
        map<int, string> visited;
        set<int> negX;

        vector <set <int> > leaves(originalVarCount + 1);
       // processTseitins (leaves);
        //DTNode *root = decStack.top().getDTNode();
	    ofstream ofs (baseFileName+".syn.blif", ofstream::out);

        writeComp(ofs);

		ofs<<".model DS"<<endl;
		ofs<<".inputs ";
		DepositOfVars::iterator v_it;
        //cout << " OriginalVarCount : " << originalVarCount << endl;
		for (int i = 1; i <= originalVarCount; i++)
		{
			ofs<<getInputName(i)<<" ";
			if (activeY[i] ) {
				ofs<<getInputName(i+originalVarCount)<<" ";
			}
		}
        ofs << endl;

		DTNode* root;
		if (1 == decStack.top().getDTNode()->numChildren())
			root = decStack.top().getDTNode()->onlyChild();
		else
			root = decStack.top().getDTNode();

        if (onlyXClauses.size() > 0)
		    ofs<<".outputs  DS_OUT"<<endl;
        else
		    ofs<<".outputs "<<getIDName(root->getID())<<endl;
    //Tseitins need to be handled separately

        set <int> assign;
        int tnum = 0;
        writeDSharp_rec( root, ofs, visited, negX, assign,tnum, leaves) ;

        if (onlyXClauses.size() > 0)
        {
            vector<string> children;
            children.push_back(writeOnlyX (ofs, visited, negX));
            children.push_back(visited[root->getID()]);
            writeOPtoBLIF_rec(children, 1, ofs,  "DS_OUT"); //OR
        }

		ofs<<".end"<<endl;

/*    for (int i = 1; i <= originalVarCount ; i++)
    {

        ofs <<  ".model G_" << node << endl;
        ofs<<".inputs ";
        for (auto &it: curr_leaves)
        {
            int var = abs(it);
            bool pos = (it > 0);
            if ( isActiveY[var])
            {
                if (pos)
				    ofs << " " << getInputName(i+originalVarCount);
                else
                    ofs << " " << getInputName(i);
            }
            else
                    ofs << " " << getInputName(i);

        }
        ofs << endl;
        
        ofs << " .outputs  G_OUT_" << i << endl;

     }
		//cout<<"end DS"<<endl;
        */
		writeOFF(ofs);
		writeON(ofs);
		writeOR(ofs);
		writeAND(ofs);
		writeEqual(ofs);
		writeNEG(ofs);
		writeXOR(ofs);
        ofs.close();


}


void synSolver::writeOPtoBLIF_rec(vector<string> &children, int op, ofstream& ofs,  string out)
{
		assert(children.size() > 0);

        //cout << "In writeOPtoBLIF_rec Children 0 : " << children[0] << endl;

		if(children.size() == 1)
        {
			ofs << "subckt equate equate1 = " + children[0] << " equateOut = " + out << " "  << endl;
            return;
        }
        if (op > 2)
        {
            cout << "Error: Unknown Operator"  << endl;
            return;

        }

        bool genTemp = false;

        string nv = "";
        if (children.size() > 2)
        {
            genTemp = true;
            nv = "TMP_0_" + out;
        }
        else
            nv = out;

        string curr = children[0];

        for (int i = 1; i < children.size(); i++)
        {
            if(op == 0) 
                ofs<<".subckt and and1 = "<<curr<<" and2 =  "<<children[i]<< " andOut = "<<nv<<endl;
            else if (op == 1)
                ofs<<".subckt or or1 = "<<curr<<" or2 =  "<< children[i]<< " orOut = "<<nv<<endl;
            else  
                ofs<<".subckt xor xor1 = "<<curr<<" xor2 =  "<< children[i]<< " xorOut = "<<nv<<endl;

            curr = nv;
            if(i < children.size() - 2)
            {
                nv = "TMP_" + to_string(i) + "_" + out;
            }
            else    
                nv = out;
        }
}

string synSolver::writeOnlyX(ofstream & ofs, map<int, string> & visited, set<int>& negX)
{
    vector<string> cl_children;
    vector<string> children;
    string out;

    for (int i = 0; i < onlyXClauses.size(); i++)
    {
        cl_children.resize(0);
        for (auto &it : onlyXClauses[i]) //Can only be literals of X vars
        {
            int varNum = abs(it);
            
            string name = (it > 0) ? getInputName(varNum) : "DS_INP_NEG_"+to_string(varNum);
            cl_children.push_back(name );
            if ((it < 0) && (negX.count (varNum) == 0) )
            {
			    ofs<<".subckt not neg1= "<< getInputName(varNum) <<" negOut= "<<name<<endl;
                negX.insert (varNum);
            }

        }
        out = "OX" + to_string(i);
        writeOPtoBLIF_rec(cl_children, 1, ofs,  out);
        children.push_back(out);
    }
    out = "OX_OUT";
    writeOPtoBLIF_rec(children, 0, ofs,  out);
    return out;
}
        
//Dsharp does some translation because of which the lit and the val values of a node may differ.
//We need so fix this while writing the Blif file. -SS

//void synSolver::readWriteTseitin (string tseitinFileName, ofstream &ofs)
//{
 //   ifstream ifs (tseitinFileName);
  //  if (! ifs.isopen())
   //     cout << "Could not read the tseitin file " << endl;

 

//}

string synSolver::printTseitin (ofstream& ofs, int& tnum,  int varNum, set <int>& assign, map<int, string> & tvisited, int polarity)
{

    if (tvisited.find (varNum) != tvisited.end())
        return tvisited[varNum];

     varNum = abs (varNum);
    //varNum is a Tseitin Var
    vector<int> dependents;
    vector<string> children;
    //The Tseitin var is not a constant.. already taken care of earlier.
    string out = getInputName (varNum) + "_" + to_string(tnum) ;

        cout << "Assign " << endl;
        for (auto &it: assign)
            cout << " " << it ;
        cout << endl;
            
        if (depAND.count (varNum) > 0) //it is an and node
        {
            dependents = depAND[varNum];
            

            for (auto &it:dependents)
            {
                int child = abs(it);
                bool pol = it > 0;
                 string val = pol? "off" : "on";
                
                if (activeY[child])    //dependent is a Y var
                {
                     cout << "Dependent on  " << it << endl;
                     if (assign.find(child) != assign.end())
                        cout << "Child " << it << " has an assignment!" << endl;
                     if (assign.find(-child) != assign.end())
                        cout << "-Child " << it << " has an assignment!" << endl;

                      if (assign.find(child) != assign.end() && pol)
                      {
                                cout << it << " has been set to true " << endl;
                                val = "on";
                      }
                      if (! pol && (assign.find(-child) != assign.end()))  //If the child is negative and so is the assignment
                      {
                           cout <<  pol << ": polarity " << endl;
                            val = "on";
                      }
                      
                    if (!(assign.find(child) != assign.end() || assign.find(-child) != assign.end()) ) //No assignment to this war
                    {
                        cout << "Child " << child <<  "not assigned yet" << endl;
                        val = "on"; //if the variable has not been seen yet, can give any value; Should i just set it to "off" to reduce the representation??
                    }
                    //get value of it from assign
                    
                   children.push_back(val);
                   // if (val == "off")
                    //        return "off"; // Anything conjuncted with 0 is 0.
                    //else
                     //   continue;
                }
                else
                {
                    if (tseitinY[it])
                    {
                        //What do we do if the pol is negative?

                        tnum ++;
                        val = printTseitin (ofs, tnum, child, assign, tvisited, pol );
                        if (val == "off"  )
                        {
                            if (pol)
                                return "off"; // Anything conjuncted with 0 is 0.
                        }
                        else
                        {
                            if (val == "on")
                            {
                                if (!pol)
                                    return "off"; // Anything conjuncted with 0 is 0.
                            }
                            else
                                children.push_back(val);
                        }
                 }
                 else
                 {   //for X
                    if (pol) 
                        val = getInputName(child) ;
                    else
                        val = getInputNegName(child) ;

                   children.push_back(val);
                }
            }
            
            
        }
        writeOPtoBLIF_rec(children, 0, ofs, out);
            
     }
     else if (depOR.count (varNum) > 0) //it is an and node
     { 
            dependents = depOR[varNum];
            

            for (auto &it:dependents)
            {
                int child = abs(it);
                bool pol = it > 0;
                string val = "off";
                
                if (activeY[child])    //dependent is a Y var
                {
                     cout << "Dependent on  " << it << endl;
                     if (assign.find(child) != assign.end())
                        cout << "Child " << it << " has an assignment!" << endl;
                     if (assign.find(-child) != assign.end())
                        cout << "-Child " << it << " has an assignment!" << endl;

                      if (assign.find(child) != assign.end() && pol)
                      {
                                val = "on";
                      }
                      if (! pol && (assign.find(-child) != assign.end()))  //If the child is negative and so is the assignment
                      {
                            val = "on";
                      }
                      
                    if (!(assign.find(child) != assign.end() || assign.find(-child) != assign.end()) ) //No assignment to this war
                    {
                        cout << "Child " << child <<  "not assigned yet" << endl;
                        val = "off"; //if the variable has not been seen yet, can give any value; Should i just set it to "off" to reduce the representation??
                    }
                    //get value of it from assign
                    
                   if (val == "on") // if a child is true; just return true;
                    return val;

                   children.push_back(val);
                   // if (val == "off")
                    //        return "off"; // Anything conjuncted with 0 is 0.
                    //else
                     //   continue;
                }
                else
                {
                    if (tseitinY[it])
                    {
                        //What do we do if the pol is negative?

                        tnum ++;
                        val = printTseitin (ofs, tnum, child, assign, tvisited, pol );
                        if (val == "on" && pol)
                                return "on"; // Anything disjuncted with 1 is 1
                        else
                        {
                            if (val == "off" && ( !pol ))
                                    return "on"; // Anything conjuncted with 0 is 0.
                            else
                                children.push_back(val);
                        }
                    }
                    else
                    {   //for X
                        if (pol) 
                            val = getInputName(child) ;
                        else
                            val = getInputNegName(child) ;

                    children.push_back(val);
                    }
                }
            
            
        }
        writeOPtoBLIF_rec(children, 1, ofs, out);
      }
     else if (depXOR.count (varNum) > 0) //it is an and node
     { 
            dependents = depOR[varNum];

            for (auto &it:dependents)
            {
                int child = abs(it);
                bool pol = it > 0;
                string val = "off";
                
                if (activeY[child])    //dependent is a Y var
                {
                     cout << "Dependent on  " << it << endl;

                      if (assign.find(child) != assign.end() && pol)
                      {
                                val = "on";
                      }
                      if (! pol && (assign.find(-child) != assign.end()))  //If the child is negative and so is the assignment
                      {
                            val = "on";
                      }
                      
                    if (!(assign.find(child) != assign.end() || assign.find(-child) != assign.end()) ) //No assignment to this war
                    {
                        cout << "Child " << child <<  "not assigned yet" << endl;
                        val = "on"; //if the variable has not been seen yet, can give any value; Should i just set it to "off" to reduce the representation??
                    }
                    //get value of it from assign
                    
                   children.push_back(val);
                }
                else
                {
                    if (tseitinY[it])
                    {
                        //What do we do if the pol is negative?

                        tnum ++;
                        val = printTseitin (ofs, tnum, child, assign, tvisited, pol );
                        children.push_back(val);
                    }
                    else
                    {   //for X
                        if (pol) 
                            val = getInputName(child) ;
                        else
                            val = getInputNegName(child) ;

                    children.push_back(val);
                    }
                }
            
        }
        writeOPtoBLIF_rec(children, 2, ofs, out);//xor op
      }

           // if (!pol)
            //    return getInputNegName(varNum);
        tvisited[varNum] = out;
        string negName = getInputNegName (varNum) + "_" + to_string(tnum) ;
        tvisited[-varNum] = negName;
                //print to the file - neg t = not t.
        if (polarity)
            return out;
        else
        {
			ofs<<".subckt not neg1= "<< out <<" negOut= "<< negName << endl;
            return negName;
        }
            
     return "off";
}

void synSolver::writeDSharp_rec(DTNode* node, ofstream& ofs, map<int, string> & visited, set<int>& negX, set<int>& assign, int &tnum, vector<set <int> > & leaves) {
		
		int node_id = node->getID(); // getUniqueID(node);

        cout << " At node " << node_id << endl;

		if(visited.find(node_id)!=visited.end())
        {
		    if (node->getType() != DT_LIT)
            {
                    cout <<  "Already visited node : " << node_id << "Returning " << endl;
                    return ;
            }
            else
            {
                int varNum = abs(node->getVal());
                if (!tseitinY[varNum])
                {
                    cout <<  "Already visited node : " << node_id << "Returning " << endl;
                    return ;
                }
            }
        }


		if (node->getType() == DT_TOP) {
			visited[node_id] = "on";
			return ;
		}
		else if (node->getType() == DT_BOTTOM) {
			visited[node_id] = "off";
			return ;
		}
		else if (node->getType() == DT_LIT)
        {

			bool polarity = node->getVal()>0?1:0;
            int varNum = abs(node->getVal());

           // cout << " For DT_LIT " << "varNum = " << varNum << "ID = " << node_id << endl;

	//		int varNum = abs(node->getVal());

			//if(node->isTseitin)
			//	varNum = abs(node->tseitinVar);
			
			string name = " ";

            if (!(activeY[varNum] || tseitinY[varNum]))  //Add to the component only if output variable
            {
				name = getInputName(varNum);
				if(!polarity) {
					name = "DS_INP_NEG_"+to_string(varNum);
					ofs<<".subckt not neg1= "<< getInputName(varNum) <<" negOut= "<<name<<endl;
                    negX.insert(varNum);
				}
                visited[node_id] = name;
                return;
			}
			else 
            {
                 if (activeY[varNum])
                 {
                       if(polarity)
                            name = getInputName(varNum);
                       else
                            name = getInputName(varNum+originalVarCount);

                        visited[node_id] = name;
                        assign.insert (node->getVal()); 
                        return;


                 }
                 if (tseitinY[varNum])
                 {
		            if(visited.find(node_id)!=visited.end())
                           return;
                    if (depCONST.count (varNum) != 0 || depCONST.count(-varNum) != 0) //Tseitin is a constant
                    {

                        if (depCONST.count(varNum) != 0)
                        {
					        ofs<<".subckt equate equate1 on equateOut = " << getInputName(varNum)  <<endl;
				            name = getInputName(varNum);
                        }
                        else
                        {
					            ofs<<".subckt equate equate1 off equateOut = " << getInputName(varNum)  <<endl;
				                name = getInputNegName(varNum);
                //instead of varnum print DT_BOT
                        }
                        visited[node_id] = name;
                     }
                     else
                     {
                            map < int, string> tvisited; //A visited map for tseitins at the subtree rooted at this main tseitin node
                            cout << "calling printTseitin for " << varNum << endl;
                            tnum++;
                            if (visited.find(node_id) != visited.end () && leaves[varNum].size() <= 0 )    //Already visited and does not have activeY leaves
                                return;

                            visited[node_id] = printTseitin (ofs, tnum, varNum, assign, tvisited, polarity); 
                     }
                  
                  }
            }

            cout << "Name for " << node_id << " is " << name << endl;
	    }
		else
        {
			vector<string> children;
//Need to take care of polarity! Haven;t done that -SS. TODO
            int cVal;

            //sort children based on whether they are Y, X or Tseitin or any other node
            // Y nodes first
            //rest later -- have kept Tseitin to the last 

            vector<DTNode *> sortedChildren(node->numChildren());
            int first = 0; 
          //  int last = node->numChildren() -1;
			for (auto it = node->getChildrenBegin(); it != node->getChildrenEnd(); it++) 
            {
                if ((*it)->getType() == DT_LIT && (activeY[abs((*it)->getVal())])) //Y var
                {
                     sortedChildren[first++] = *it;
                }
             }
			 
             for (auto it = node->getChildrenBegin(); it != node->getChildrenEnd(); it++) 
             {
                if (!((*it)->getType() == DT_LIT && (activeY[abs((*it)->getVal())]))) //!Y var
                {
                     sortedChildren[first++] = *it;
                }

             }
             for (auto &it :sortedChildren)
             {
			//for (auto it = node->getChildrenBegin(); it != node->getChildrenEnd(); it++) {
                if (it->getType () !=  DT_LIT)
                {
                    set <int> newassign = assign;
                    writeDSharp_rec(it, ofs, visited, negX, newassign, tnum, leaves);
                }
                else
                    writeDSharp_rec(it, ofs, visited, negX, assign, tnum, leaves);
          //      cout << "Adding child " <<  (*it)->getID() << " i.e.,  " <<  visited[(*it)->getID()] << " to children of " << node_id << endl;
				children.push_back(visited[it->getID()] );
			}
			
			if(children.size()!=0)
            {
            //    cout << "Calling writeOP for " << node_id << endl;
            //    for (auto &it : children)
           //         cout << "Child : " << it << " "  ;
           //         cout << endl;
                int nt = (node->getType()==DT_AND)? 0 : 1;
                    
				writeOPtoBLIF_rec(children, nt, ofs, getIDName(node_id)); //Check what this should be -- not sure SS
			}
            else
                cout << "Internal node with 0 children " << node_id << ". Check might be an error " << endl;

			//cout << "Visited! Adding " << getIDName(node_id) << endl;
			visited[node_id] = getIDName(node_id);
		}

	}
//	}


	void synSolver::instantiateOnOff(ofstream & ofs) {
		ofs<<".subckt onM onOut=on"<<endl;
		ofs<<".subckt offM offOut=off"<<endl;
	}

	string synSolver::getInputName(int var) {
		return "DS_INP_"+ to_string(var);
	}
	string synSolver::getInputNegName(int var) {
		return "DS_INP_NEG_"+ to_string(var);
	}
	string synSolver::getIDName(int id) {
		return "DS_"+ to_string(id);
	}
	/*string synSolver::writeDTree(ofstream& ofs) {
		ofs<<".model DS"<<endl;
		ofs<<".inputs ";
		DepositOfVars::iterator v_it;
        for (int i = 0; i < varsX.size();  i++)
		{
				ofs<<getInputName(i)<<" ";
        }

//Tseitin's - how should they be written?
    //    for (auto; i< varsY.size(); i++) //Use varsY or activeY?
        for (auto &it: activeYVars)
        {
				ofs<<getInputName(it)<<" ";
				ofs<<getInputNegName(it+originalVarCount)<<" ";
	    }
        //for (int i = 0; i< varsY.size(); i++) //Use varsY or activeY?
		//		ofs<<getInputNegName(i+originalVarCount)<<" ";

		//for (auto s : extraTseitins)
		//	ofs<<s<<" ";
		//ofs<<endl;

		DTNode* root;
		if (1 == decStack.top().getDTNode()->numChildren())
			root = decStack.top().getDTNode()->onlyChild();
		else
			root = decStack.top().getDTNode();

		ofs<<".outputs "<<getIDName(root->getID())<<endl;
		map<int, string> visited;

		instantiateOnOff(ofs);

		// cout<<"rootID "<<root->getID()<<endl;
		writeDSharp_rec( root, ofs, visited);

		ofs<<".end"<<endl;
		cout<<"end DS"<<endl;

		return "";
	}
    */
    
	void  synSolver::writeAND(ofstream& ofs) {
		ofs<<".model and"<<endl;
		ofs<<".inputs and1 and2"<<endl;
		ofs<<".outputs andOut"<<endl;
		ofs<<".names and1 and2 andOut"<<endl;
		ofs<<"11 1"<<endl;
		ofs<<".end"<<endl;
	}


	void  synSolver::writeXOR(ofstream& ofs) {
		ofs<<".model xor"<<endl;
		ofs<<".inputs xor1 xor2"<<endl;
		ofs<<".outputs xorOut"<<endl;
		ofs<<".names xor1 xor2 xorOut"<<endl;
		ofs<<"10 1"<<endl;
		ofs<<"01 1"<<endl;
		ofs<<".end"<<endl;
	}

	void  synSolver::writeOR(ofstream& ofs) {
		ofs<<".model or"<<endl;
		ofs<<".inputs or1 or2"<<endl;
		ofs<<".outputs orOut"<<endl;
		ofs<<".names or1 or2 orOut"<<endl;
		ofs<<"1- 1"<<endl;
		ofs<<"-1 1"<<endl;
		ofs<<".end"<<endl;
	}

	void  synSolver::writeNEG(ofstream& ofs) {
		ofs<<".model not"<<endl;
		ofs<<".inputs neg1"<<endl;
		ofs<<".outputs negOut"<<endl;
		ofs<<".names neg1 negOut"<<endl;
		ofs<<"0 1"<<endl;
		ofs<<".end"<<endl;
	}

	void  synSolver::writeEqual(ofstream& ofs) {
		ofs<<".model equate"<<endl;
		ofs<<".inputs equate1"<<endl;
		ofs<<".outputs equateOut"<<endl;
		ofs<<".names equate1 equateOut"<<endl;
		ofs<<"1 1"<<endl;
		ofs<<".end"<<endl;
	}


	void synSolver:: writeON(ofstream& ofs){
		ofs<<".model onM"<<endl;
		ofs<<".outputs onOut"<<endl;
		ofs<<".names onOut"<<endl;	
		ofs<<"1"<<endl;
		ofs<<".end"<<endl;
	}

	void synSolver:: writeOFF(ofstream& ofs) {
		
		ofs<<".model offM"<<endl;
		ofs<<".outputs offOut"<<endl;
		ofs<<".names offOut"<<endl;	
		ofs<<".end"<<endl;	
	}




