#include "synNNF.h"


synSolver::synSolver()
{
    varsX.clear();
    varsY.clear();
    tseitinVars = 0;

}

void synSolver::init()
{
    int Y;
    bool containsActY = false;
    cout << " Size of all Clauses " << allClauses.size() << endl;
    for (int i = 0; i < allClauses.size(); i++)
    {
                containsActY = false;  

                for (int j = 0; j < allClauses[i].size(); j++)
                {
                        Y = abs (allClauses[i][j]);               
                        if (find(varsY.begin(), varsY.end(), Y) != varsY.end() )
                        {
                            containsActY = true;  
                            if ( activeY.find(Y) == activeY.end())
                            {
                                activeY.insert (Y);
                            }
                        }
                }
                if (containsActY)
                    workingClauses.push_back(allClauses[i]);

             //   cout << " Size of workingClauses " << workingClauses.size() << endl;
                 onlyXClauses.push_back(! containsActY);


                 //workingClauses.push_back(containsActY);
         //}
    }
    cout << " ActiveY "  ;
    for (auto &it: activeY)
             cout << it << " " ;
    cout << endl;
}

void synSolver::CreateSynNNF(vector<vector<int> > &cls, vector<int>& Xvar, vector<int>& Yvar, vector<bool>& TseitinCls)
{
        cout << " In CreateSynNNF" << endl;
        allClauses = cls;
        varsX = Xvar;
        varsY = Yvar;
        tseitinClauses = TseitinCls;
        //set<int> actY; 

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
        
        cout << "Size of actY " << activeY.size() << endl;

        for (auto &it: theVars)
        {
            CVariableVertex c = it;
           // if (find (varsY.begin(), varsY.end(), c.getiVarNum()) != varsY.end())
            //    c.outputVar = true;
        }
        solve (NULL);

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
		if (decStack.TOS_countRemComps() == 0)
		{
			handleSolution();
			return false;
		}
	}

    if (OnlyX(decStack.TOS_NextComp()))
    {
        cout << " num_Nodes = " << num_Nodes << endl;
        decStack.top().getDTNode()->print();
        
        CComponentId & refSupComp = decStack.TOSRefComp();
        if (refSupComp.countCls() > 1)
        {
            DTNode * newNode = new DTNode(DT_AND, num_Nodes++);
            //add the literals corresponding to the clauses containing Xvar


            vector<ClauseIdT>::const_iterator itCl;
            int numVar = 0;
            for (itCl = refSupComp.clsBegin(); *itCl != clsSENTINEL; itCl++)
            {
                    LiteralIdT *prev = NULL;
                    DTNode *cl = new DTNode (DT_OR, num_Nodes++);
                    numVar = 0;
                    for (vector<LiteralIdT>::iterator itX = begin(getClause(*itCl)); *itX != ClauseEnd(); itX++)
                    {
                        LiteralIdT curr = *itX;
                        if (getVar(*itX).isActive  ())
                        {
                            numVar ++;
                            if (prev == NULL)
                                prev = & *itX;
                            else
                            {
                                DTNode *litNode = get_lit_node (curr.toSignedInt());
                                litNode->addParent(cl, true);
                             }
                        }
                        if (prev != NULL)
                        {
                            DTNode *prevNode = get_lit_node (prev->toSignedInt());
                            if (numVar > 1)
                            {
                                   prevNode->addParent(cl, true);
                                   cl->addParent(newNode, true);
                            } 
                            else
                            {
                                   prevNode->addParent(newNode, true);
                            }
                        }

                    }
            }

            newNode->addParent(decStack.top().getCurrentDTNode(), true);
            decStack.push(newNode);
            bcpImplQueue.clear();
            bcpImplQueue.push_back(AntAndLit(NOT_A_CLAUSE, theLit));
            return true;

        }
        else
            cout << "Empty Component " << endl;
    }
        
	if (!findVSADSDecVar(theLit, decStack.TOS_NextComp())
			|| decStack.TOS_NextComp().getClauseCount() == 0) // i.e. component satisfied
	{
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

	return true;
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

    cout << "RefSupComp " ;
    printComponent(refSupComp);
    cout << endl;
	for (itCl = refSupComp.clsBegin(); *itCl != clsSENTINEL; itCl++)
	{
		lookUpCls[*itCl] = IN_SUP_COMP;
	}

	for (vt = refSupComp.varsBegin(); *vt != varsSENTINEL; vt++)
	{
		if (getVar(*vt).isActive())
        {
            //if ((activeY.find(getVar(*vt).getVarNum()) != activeY.end()))
		    //{
                lookUpVars[*vt] = IN_SUP_COMP;
                getVar(*vt).scoreDLIS[true] = 0;
                getVar(*vt).scoreDLIS[false] = 0;
   		    //}
         }
	}

	componentSearchStack.clear();
	
	for (vt = refSupComp.varsBegin(); *vt != varsSENTINEL; vt++)
    {
    //What happens if only  X vars are present in refSupComp
		    if (lookUpVars[*vt] == IN_SUP_COMP && activeY.find(*vt) != activeY.end() )
		    {
			    decStack.TOS_addRemComp();
			    decStack.lastComp().setTrueClauseCount(0);
                lookUpVars[*vt] = SEEN;
            	componentSearchStack.push_back(*vt);
            //    cout << "Added " << *vt << " to comp stack" << endl;
			    getComp(*vt, decStack.TOSRefComp(), lookUpCls, lookUpVars);
			    decStack.lastComp().addVar(varsSENTINEL);
			    decStack.lastComp().addCl(clsSENTINEL);
                //cout << "new component ";
                //printComponent (decStack.lastComp());
                //cout << endl;
   		    }
                
    }
	decStack.TOS_sortRemComps();
	return true;
}

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

	for (vt = superComp.varsBegin(); *vt != varsSENTINEL; vt++)
    {

    }
	for (vt = componentSearchStack.begin(); vt != componentSearchStack.end(); vt++)
	// the for-loop is applicable here because componentSearchStack.capacity() == countAllVars()
	{
		pActVar = &getVar(*vt);
		//BEGIN traverse binary clauses
		for (itL = pActVar->getBinLinks(true).begin(); *itL != SENTINEL_LIT; itL++)
			if (lookUpVars[itL->toVarIdx()] == IN_SUP_COMP )
			{
				nBinClsSeen++;
				lookUpVars[itL->toVarIdx()] = SEEN;
                if (activeY.find(itL->toVarIdx()) != activeY.end()) //Add to the component only if output variable
                {
				    componentSearchStack.push_back(itL->toVarIdx());
				    getVar(*itL).scoreDLIS[itL->polarity()]++;
				    pActVar->scoreDLIS[true]++;
              //      cout << "Adding " << itL->toVarIdx() << "comp of " << pActVar->getVarNum() << endl;
                }
			}
		for (itL = pActVar->getBinLinks(false).begin(); *itL != SENTINEL_LIT; itL++)
			if (lookUpVars[itL->toVarIdx()] == IN_SUP_COMP)
			{
				nBinClsSeen++;
				lookUpVars[itL->toVarIdx()] = SEEN;
                if (activeY.find(itL->toVarIdx()) != activeY.end())
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
                          //  cout << "Var *itL is satisfied " << endl;
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
                           if (activeY.find(itL->toVarIdx()) != activeY.end())
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
           // cout << "Adding var " << *vt << " to lastComp " << endl;
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
        cout << " Considering variable " << getVar(*it).getVarNum()<< ". Lit id: (T) " << getVar(*it).getLitIdT(true).toSignedInt() << ". Lit id: (F):" << getVar(*it).getLitIdT(false).toSignedInt() << endl;
        cout << " It is in activeY : " << (activeY.find(getVar(*it).getVarNum()) != activeY.end()) << endl;
		if (getVar(*it).isActive()  && (activeY.find(getVar(*it).getVarNum()) != activeY.end()))
		{
			bo = (int) getVar(*it).getVSIDSScore() + getVar(*it).getDLCSScore();

			if (bo > score)
			{
				score = bo;
				pVV = &getVar(*it);
			}
            //cout << " bo: is " << bo << endl;
			
			if (0 != priorityVars.count(getVar(*it).getVarNum()))
			{
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

	if (pVV == NULL)
		return false;

	bool pol = pVV->scoreDLIS[true] + pVV->scoreVSIDS[true]
			> pVV->scoreDLIS[false] + pVV->scoreVSIDS[false];

	theLit = pVV->getLitIdT(pol);

	return true;
}
bool synSolver::OnlyX (const CComponentId & superComp)
{
	    vector<VarIdT>::const_iterator it;
        int numVar = 0;
	    for (it = superComp.varsBegin(); *it != varsSENTINEL; it++)
        {
            numVar++;
		    if (getVar(*it).isActive())
            {
                if (activeY.find(getVar(*it).getVarNum()) != activeY.end())
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

        cout << "Processing clause " << i << endl;
      //  while (it != clauses[i].end())
       // {
            cout << *it << endl;

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

// unsigned int synSolver::makeVariable(unsigned int VarNum)
//{
 //       cout << " First calling instancegraph make Variable " << endl;
  //      CInstanceGraph::makeVariable (VarNum);
        //Add if Y var then output == true;
//}

