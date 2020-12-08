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
    //cout << " Size of all Clauses " << allClauses.size() << endl;

    int numVars = varsX.size() + varsY.size();
    activeY.resize(numVars+1, 0); //All vars not active to begin with
    tseitinY.resize(numVars+1, 0); //All vars not tseitin to begin with

    for (auto &it: tseitinVars)
        tseitinY[it] = true; //Assigning true to TseitinVars

    for (auto &it : varsY)
    {
         //Temporary Comment  - to check how things work.
        //activeY[it] = true;
        //this->priorityVars.insert(it);
        if (! tseitinY[it])
        {
            activeY[it] = true;
        //    this->priorityVars.insert(it);
        }
    }

    //print priorityVars
    set <int> uOClause; //original unary clauses
    for (int i = 0; i < allClauses.size(); i++)
    {
                //if (tseitinClauses[i])  //Ignore the clause as it is a tseitin clause
                 //   continue;   
                containsActY = false;  

                //cout << " Clause " << i ;
                if (allClauses[i].size() == 1)  //collect the constants -- 
                {
                    uOClause.insert (allClauses[i][0]);
                }
                else
                {
                    for (int j = 0; j < allClauses[i].size(); j++)
                    {
                        Y = abs (allClauses[i][j]);               
                        
                        //cout << " " << allClauses[i][j] ;
                        if (activeY[Y] || tseitinY[Y])
                            containsActY = true;
                    }
         //       cout << endl ;
                    if (containsActY)
                        workingClauses.push_back(allClauses[i]);
                    else
                    {
                        onlyXClauses.push_back(allClauses[i]);
                    //    cout << "Clause" << i << "contains only X vars " << endl;
                    }

                    //cout << " Size of workingClauses " << workingClauses.size() << ". Size of onlyX clauses "  << onlyXClauses.size() << endl;
                }

    }
//Now handle the constants -- Does a constant X make sense?
    for (auto &it : depCONST)
    {
        vector <int> uClause ;
        uClause.push_back (it);
        if (activeY[abs(it)] || tseitinY[abs(it)])
        {
              workingClauses.push_back(uClause);
              //cout << "Added " << it << " 0 " << " to workingClauses" << endl;
        }
        else
        {
             onlyXClauses.push_back(uClause);
             //cout << "Added " << it << " 0 " << " to Xclauses" << endl;
        }
        if (uOClause.find(it) != uOClause.end())
            uOClause.erase (it);
    }
    assert (uOClause.size () == 0); //all original unary clauses covered.
    //cout << " ActiveY "  ;
    //for (auto &it: activeYVars)
     //        cout << it << " " ;
    //cout << endl;
}

void synSolver::CreateSynNNF(vector<vector<int> > &cls, vector<int>& Xvar, vector<int>& Yvar, vector<bool>& TseitinCls, vector<int> & tVars, string fileName, set <int> & dc, map<int, vector<int> > & da, map<int, vector<int> > & dor, map<int, vector<int> > & dx)
{
        //cout << " In CreateSynNNF" << endl;
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
        //cout << "X: " ;
        //for (int j = 0; j < Xvar.size(); j++)
         //    cout << Xvar[j] << " " ;
        //cout << endl;
        //cout << "Y: " ;
        //for (int j = 0; j < Yvar.size(); j++)
         //        cout << Yvar[j] << " " ;
        //cout << endl;
            init ();
         //   cout << " Init done. Calling createfromPrep " << endl;

            createfromPrep( workingClauses, Xvar.size() + Yvar.size()); //Create the data structures;
          //    cout << " Size of workingClauses " << workingClauses.size() << endl;
            
           // cout << "Size of actY " << activeYVars.size() << endl;

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
        //cout << "Num. of remaining comps " << (unsigned int) decStack.TOS_countRemComps() << endl;
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
            cout << " findVSADDecVar returned false. No Y variable left in the component " << endl;

            if (OnlyXandTseitin(decStack.TOS_NextComp()))
            {
                attachComponent();
                handleSolution();
                decStack.TOS_popRemComp();
                return false;
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

    //cout << "Printing Decision Tree with " << theLit.toSignedInt() << endl;
    //decStack.top().getCurrentDTNode()->print(); 
	return true;
}
void synSolver::attachComponent()
{
    
	LiteralIdT theLit(NOT_A_LIT);
    vector <LiteralIdT> allLits;
       decStack.top().getDTNode()->print(5);
        
        CComponentId & refSupComp = decStack.TOSRefComp();
        cout << "In attach Component. RefsupComp " << refSupComp.id << endl;
        if (refSupComp.countCls() > 1)
        {
            DTNode * newNode = new DTNode(DT_AND, num_Nodes++);
            //add the literals corresponding to the clauses containing Xvar


            vector<ClauseIdT>::const_iterator itCl;
            vector<VarIdT>::const_iterator itV;
	        vector<LiteralIdT>::const_iterator itL;
            int numVar = 0;
            bool allSatCl = true;

	        CVariableVertex * pActVar;

           //first need to go through the binary links
	        vector<VarIdT>::const_iterator vt;

            for (itCl = refSupComp.clsBegin(); *itCl != clsSENTINEL; itCl++)
            {
                cout << "printing Active Clause " << *itCl << endl;
                //printClause (*itCl);
                //cout << endl;
                printActiveClause (*itCl);
                cout << endl;
                if (isSatisfied(*itCl))
                    cout << "Clause above is satisfied " << endl;
				if (!isSatisfied(*itCl))
                {
                    allSatCl = false;
                    LiteralIdT *prev = NULL;
                    DTNode *cl = new DTNode (DT_OR, num_Nodes++);
                    numVar = 0;
                    
                    for (vector<LiteralIdT>::iterator itX = begin(getClause(*itCl)); *itX != ClauseEnd(); itX++)
                    {
                        LiteralIdT curr = *itX;
                        allLits.push_back(curr);

                        if (getVar(*itX).isActive  ())
                        {
                           // cout << "Clause  " << *itCl << " Var " << curr.toSignedInt() << endl;
                            //cout << "Lit " << curr.toSignedInt() << " " ;
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
                     }
                        
                     if (prev != NULL)
                     {
                            DTNode *prevNode = get_lit_node (prev->toSignedInt());
                            if (numVar > 1)
                            {
                                   cl->addParent(newNode, true);
                                   prevNode->addParent(cl, true);
                                   //cout << "Printing new clauses " <<endl;
                                   cl->print();
                                   cout << endl;
                            } 
                            else
                            {
                                   prevNode->addParent(newNode, true);
                                   prevNode->print();
                                   cout << endl;
                                   //cout << "Printing prev node" << endl;
	                               bcpImplQueue.push_back(AntAndLit(NOT_A_CLAUSE, *prev));
                            }
                       }
                        

                    }
                    //if (numVar > 0 )
                     //   cl->addParent(newNode, true);
                 }
                 cout << "Considering Binary Clauses now " << endl;
	             for (vt = componentSearchStack.begin(); vt != componentSearchStack.end(); vt++)
                 {
                        pActVar = &getVar(*vt);
                //BEGIN traverse binary clauses
                        for (itL = pActVar->getBinLinks(true).begin(); *itL != SENTINEL_LIT; itL++)
                        {
                                int origVar = origTranslation[itL->toSignedInt()];
                                if (getVar (*itL). isActive () && ! (activeY[origVar])) //Not a Y var
                                {
                                        //cout << "Binary clause between " << *vt  << " and "  << itL->toSignedInt() << endl;
                                        if ( abs (itL->toSignedInt()) > abs(pActVar->getLitIdT(true).toSignedInt()))     //Check!!
                                        {
                                            DTNode *cl = new DTNode (DT_OR, num_Nodes++);
                                            DTNode *litNode = get_lit_node (itL->toSignedInt());
                                            litNode->addParent(cl, true);
                                            litNode = get_lit_node (pActVar->getLitIdT(true).toSignedInt());
                                            litNode->addParent(cl, true);
                                            cl->addParent(newNode, true);
                                            allSatCl = false;
                                         }
                                }
                        }
                        for (itL = pActVar->getBinLinks(false).begin(); *itL != SENTINEL_LIT; itL++)
                        {
                                int origVar = origTranslation[itL->toSignedInt()];
                                if (getVar (*itL). isActive () && ! (activeY[origVar])) //Not a Y var
                                {
                                         //   cout << "Binary clause between " << *vt  << " (false) and "  << itL->toSignedInt() << endl;
                                        if ( abs(itL->toSignedInt()) > abs(pActVar->getLitIdT(true).toSignedInt()))     //Check!!
                                        {
                                            DTNode *cl = new DTNode (DT_OR, num_Nodes++);
                                            DTNode *litNode = get_lit_node (itL->toSignedInt());
                                            litNode->addParent(cl, true);
                                            litNode = get_lit_node (pActVar->getLitIdT(false).toSignedInt());
                                            litNode->addParent(cl, true);
                                            cl->addParent(newNode, true);
                                            allSatCl = false;
                                        }
                                        //Should we add to the BPQueue?
                                }
                        }
                 }
	             
         //   printTree();
         if (!allSatCl)
         {
            newNode->addParent(decStack.top().getCurrentDTNode(), true);
            cout << "Printing comp tree  " <<endl;
           newNode->print();
           cout << endl;
           // decStack.push(newNode);
         }
         cout << "Printing decStack top node " << endl;
          decStack.top().getDTNode()->print(5);
           cout << endl;
        }
        else
            cout << "Empty Component " << endl;
 }

//Assigning Tseitin vars as True temporarily.


bool synSolver::recordRemainingComps()
{
    //cout << " In recordRemainingComps in synSolver " << endl;
	CComponentId & refSupComp = decStack.TOSRefComp();

	viewStateT lookUpCls[getMaxOriginalClIdx() + 2];
	viewStateT lookUpVars[countAllVars() + 2];

	memset(lookUpCls, NIL, sizeof(viewStateT) * (getMaxOriginalClIdx() + 2));
	memset(lookUpVars, NIL, sizeof(viewStateT) * (countAllVars() + 2));

	vector<VarIdT>::const_iterator vt;
	vector<ClauseIdT>::const_iterator itCl;

   // cout << "RefSupComp "  << refSupComp.id << endl;
    
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
    bool newComp = false;
    bool otherVars = false;
	
    for (vt = refSupComp.varsBegin(); *vt != varsSENTINEL; vt++)
      {
        //What happens if only  X vars are present in refSupComp
                //cout << "In recordRemComps " << getLitIdT(true).toSignedInt()*vt << endl;
               // cout << "in RRC: var " << *vt << " lit: " << getVar(*vt).getLitIdT(true).toVarIdx() << endl;
                int origVar = origTranslation[getVar(*vt).getLitIdT(true).toSignedInt()];
                //cout << "OrigVar " << origVar << endl;
                
                if (lookUpVars[*vt] == IN_SUP_COMP )
                {
                    if(activeY[origVar]  || tseitinY[origVar])
                    {
                        //cout << "Added " << *vt << " to comp stack" << endl;
                        decStack.TOS_addRemComp();
                        decStack.lastComp().setTrueClauseCount(0);
                        lookUpVars[*vt] = SEEN;
                        componentSearchStack.push_back(*vt);
                        getComp(*vt, decStack.TOSRefComp(), lookUpCls, lookUpVars);
                        decStack.lastComp().addVar(varsSENTINEL);
                        decStack.lastComp().addCl(clsSENTINEL);
                        //cout << "new component " << decStack.lastComp().id << endl;
                        newComp = true;
                        //printComponent (decStack.lastComp());
                        //cout << endl;
                    }
                    else
                    {
                       // cout << "var " << *vt << " in lookupVars but is an X var" << endl;
                        otherVars = true;

                    }
                    
                }
        }
        //cout << " new component " << newComp << " -- otherVars " << otherVars << endl;
        if (!newComp && otherVars)
                attachComponent();

	decStack.TOS_sortRemComps();
	return true;
}
/*
//Component for X and Tseitin Vars. 
void synSolver::getCompInputsAndTseitin(const CComponentId &superComp,
		viewStateT lookUpCls[], viewStateT lookUpVars[])
{
                    eout << "Added " << *vt << " to comp stack" << endl;
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
                int origVar = origTranslation[itL->toSignedInt()];
                if (activeY[origVar]  || tseitinVars[origVar])  //Add to the component only if output variable
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
                int origVar = origTranslation[itL->toSignedInt()];
                if (activeY[origVar] || tseitinVars[origVar])  //Add to the component only if output variable
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
                          // cout << itL->toVarIdx() << " is NIL  in " << *itCl << endl;
						if (!isSatisfied(*itL))
                        {
                           //cout << "clause " <<  (*itL).toSignedInt() << " is not satisfied " << endl;
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

						getVar(*itL).scoreDLIS[itL->polarity()]++;
						if (lookUpVars[itL->toVarIdx()] == IN_SUP_COMP )
						{
							lookUpVars[itL->toVarIdx()] = SEEN;
                      //      cout << " Changing lookUpVars for " << itL->toVarIdx() << " to seen " << endl;
                                int oVar = origTranslation[itL->toSignedInt()];
                                if (activeY[itL->toVarIdx()]  || tseitinVars[itL->toVarIdx()])  //Add to the component only if output variable
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
            //cout << "Adding var " << *vt << " to lastComp " << endl;
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
         //   cout << "Adding clause " << *itCl << " to lastComp " << endl;
          //  printClause (*itCl);
           // cout << endl;
		}
	//decStack.lastComp().addCl(clsSENTINEL); // Moved to above
	
	decStack.lastComp().addTrueClauseCount(nClausesSeen + nBinClsSeen);
    //cout << "No of clauses in comp " <<  nClausesSeen + nBinClsSeen << endl;

   // cout <<" Added new component to decStack " << endl;
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
    //cout << "In findVSADSDecVar in SynSolver" << endl;

	vector<VarIdT>::const_iterator it;

	int score = -1;
	int pr_score = -1;
	int bo;
	PVARV pVV = NULL;
	PVARV pr_pVV = NULL;

	for (it = superComp.varsBegin(); *it != varsSENTINEL; it++)
    {
        int oVar = getVar(*it).getLitIdT(true).toSignedInt();
		if (getVar(*it).isActive()  && activeY[oVar]) //decide only on output vars (tseitinVars are excluded from this
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
                //cout << " Is a priority Var " << endl;
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

	if (pVV == NULL ) // || pr_score == -1 ) //We want to branch only on Y variables... 
		return false;

	bool pol = pVV->scoreDLIS[true] + pVV->scoreVSIDS[true]
			> pVV->scoreDLIS[false] + pVV->scoreVSIDS[false];

	theLit = pVV->getLitIdT(pol);

	return true;
}
//Return true if it contains only X and Tseitin Vars. We cannot decide on these and hence just attach the component.
bool synSolver::OnlyXandTseitin (const CComponentId & superComp)
{
	    vector<VarIdT>::const_iterator it;
        int numVar = 0;
	    for (it = superComp.varsBegin(); *it != varsSENTINEL; it++)
        {
            numVar++;
            int oVar = getVar(*it).getLitIdT(true).toSignedInt();
		    if (getVar(*it).isActive())
            {
                if ( activeY[oVar] ) //|| tseitinVars[*it])
                    return false;
            }
         }
         cout << " Component contains only  X and Tseitin Variables " << endl;
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
            //cout << " ilitA " << ilitA << " ilitB " << ilitB << endl;

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

            printClause (idCl);

//            for (int vp = 0; vp < varPosMap.size(); vp++)
 //               cout << "VarPosMap Element "   << vp << " is " << varPosMap [vp] << endl;
    }

    //cout << " Intitializing the INcls Vector " << endl;
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
           // printClause (*clt);
			theInClsVector.push_back(*clt);
		}

		getVar(i).setInClsVecOfs(true, theInClsVector.size());
		for (clt = _inClLinks[1][i].begin(); clt != _inClLinks[1][i].end(); clt++)
		{
            //printClause (*clt);
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
	//for (int i = 0; i < varPosMap.size(); i++)
     //   cout << "origTranslation " << i << " = " << origTranslation[i] << "varPosMap " << varPosMap[i] << endl;

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
		for(int i=1; i<=originalVarCount; i++)
        {
            if (activeY[i])  //Add to the component only if output variable
            {
				string posStr = "C_OUT_"+to_string(i);
				string negStr = "C_OUT_NEG_"+to_string(i);
                ofs << ".subckt not neg1 = " << posStr << " negOut = " <<  negStr << endl;

            }
        }
		ofs<<".subckt DS ";
		for(auto q: inputsToDS) {
			ofs<<q.first<<"="<<q.second<<" ";
		}

		DTNode* root;
		if (1 == decStack.top().getDTNode()->numChildren())
			root = decStack.top().getDTNode()->onlyChild();
		else
			root = decStack.top().getDTNode();

        if (onlyXClauses.size() > 0 ) 
		    ofs<<"DS_OUT = FHAT"<<endl;
        else
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
        //cout << "Leaf Node " <<  node << endl;
        
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
            //if (activeY[it]) //Adding X for printTseitinModules. Need tochange printTseitin
                curr_leaves.insert(l);
        //    cout << "Added " << l << " to leaves " << " of " << node << endl;
        }
    } 
    leaves[node] = curr_leaves;

    visited [node] = true;
    return;
}



void synSolver::printSynNNF ()
{
        map<int, string> visited;
        set<int> negXT;

        vector <set <int> > leaves(originalVarCount + 1);
        processTseitins (leaves);
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

        //if (onlyXClauses.size() > 0 || depCONST.size() > 0 ) 
        if (onlyXClauses.size() > 0 ) 
		    ofs<<".outputs  DS_OUT"<<endl;
        else
		    ofs<<".outputs "<<getIDName(root->getID())<<endl;
    //Tseitins need to be handled separately

        ofs << ".subckt onM onOut = on" << endl;
        ofs << ".subckt offM offOut = off" << endl;
        set <int> assign;

        for (auto &it :depCONST)
        {
                assign.insert (it); //Constants are already assigned :)
        }
        int tnum = 0;
        map <string, string> tseitinVisited;
        vector<string> printT;
        writeDSharp_rec( root, ofs, visited, negXT, assign,tnum, leaves, tseitinVisited, printT) ;
        string currRoot = visited[root->getID()];
       /* if (depCONST.size () > 0)
        {
            vector<string> children;
            children.push_back(visited[root->getID()]);
            for (auto &it : depCONST)
            {
                if (it > 0)
                    children.push_back(getInputName (it));
                else
                    children.push_back(getInputNegName (abs(it)));
            }
            currRoot =  (onlyXClauses.size() > 0 ) ? "DS_WC_OUT" : "DS_OUT"; //DS with constants
            writeOPtoBLIF_rec(children, 0, ofs,  currRoot); //OR
        }
        */

        if (onlyXClauses.size() > 0)
        {
            vector<string> children;
            children.push_back(writeOnlyX (ofs, visited, negXT));
            children.push_back(currRoot);
            writeOPtoBLIF_rec(children, 0, ofs,  "DS_OUT"); //OR
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
        printTseitinModules (ofs, leaves);
		writeOFF(ofs);
		writeON(ofs);
		writeOR(ofs);
		writeAND(ofs);
		writeEqual(ofs);
		writeNEG(ofs);
		writeXOR(ofs);
        ofs.close();


}
//op = 0 == AND, op = 1 ==OR, op = 2 == EXOR
void synSolver::printTseitinModulesForOperators (ofstream & ofs,  vector<set <int> > & leaves, int op, int Tvar,  vector<int>& dependents)
{  
        vector <string> children;
		int var = abs(Tvar);
        string name = "T_" + to_string (var);
        ofs << ".model " <<  name << endl;
        ofs << ".inputs " ;
        
        if (leaves [var].size() <= 0)
            cout << " Error ! No leaves for " << var << endl;
		for(auto&it2:leaves[var])
        {
			    ofs << name << "_INP_" << to_string(abs(it2)) << " ";
        }
        ofs << endl;
        string out =  name +  "_OUT" ;
        ofs << ".outputs " << out  <<  endl;

		for(auto&it2:dependents)
        {
                int count = 0;
                int child = abs (it2);
                string child_name = to_string(child) + "_C_" +  to_string (count ++ );
                //cout << " Child " << child_name << " is a child " << endl;
                int pol = it2 > 0;

                if (tseitinY[child] )
                {
                        if (depCONST.find (count) != depCONST.end() || depCONST.find(-count) != depCONST.end()) //It is a constant
                        {

                            if (pol)
                                children.push_back((name + "_INP_" + to_string(child)));
                            else 
                            {
                                string c_name = name + "_INP_" + to_string(child);
                                string child_neg_name = name + "_NEG_INP_" + to_string(child);
                                ofs<<".subckt not neg1= "<< child_name <<" negOut= "<< child_neg_name <<endl;
                                children.push_back(child_neg_name);
                            }
                         }
                         else    
                         {
                                string depname = "T_" + to_string(child);
                                ofs << ".subckt " << depname << " " ;
                                for (auto &it3 : leaves [child])
                                {
                                    ofs << depname  << "_INP_" << abs(it3) << " = " << name << "_INP_" << abs(it3) << " ";
                                }
                                ofs <<  depname << "_OUT = " << child_name << endl;


                               if (! pol)
                               {
                                        string child_neg_name = child  + "_NEG_C_" +  to_string (count ++ );
                                        ofs<<".subckt not neg1= "<< child_name <<" negOut= "<< child_neg_name <<endl;
                                        children.push_back(child_neg_name);
                               }
                               else
                                     children.push_back(child_name);
                         }
                     
                }
                else //it is a leaf -- need to see what to do here
                {
                        children.push_back (  name + "_INP_" + to_string(child));
                }
        }
        writeOPtoBLIF_rec(children, op, ofs,   out);
        ofs << ".end" << endl;
}

void synSolver::printTseitinModules (ofstream & ofs,  vector<set <int> > & leaves)
{  

	for(auto&it: depAND) {
        printTseitinModulesForOperators ( ofs,   leaves, 0, it.first, it.second);
	}

	for(auto&it: depOR) {
        printTseitinModulesForOperators ( ofs,   leaves, 1, it.first, it.second);
	}
	for(auto&it: depXOR) {
        printTseitinModulesForOperators ( ofs,   leaves, 2, it.first, it.second);
	}

}
void synSolver::writeOPtoBLIF_rec(vector<string> &children, int op, ofstream& ofs,  string out)
{
		assert(children.size() > 0);

        //cout << "In writeOPtoBLIF_rec Children 0 : " << children[0] << endl;

		if(children.size() == 1)
        {
			ofs << ".subckt equate equate1 = " + children[0] << " equateOut = " + out << " "  << endl;
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

string synSolver::writeOnlyX(ofstream & ofs, map<int, string> & visited, set<int>& negXT)
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
            if ((it < 0) && (negXT.count (varNum) == 0) )
            {
			    ofs<<".subckt not neg1= "<< getInputName(varNum) <<" negOut= "<<name<<endl;
                negXT.insert (varNum);
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


void synSolver::writeDSharp_rec(DTNode* node, ofstream& ofs, map<int, string> & visited, set<int>& negXT, set<int>& assign, int &tnum, vector<set <int> > & leaves, map <string, string>& tseitin_visited, vector<string>& printT) {
		
		int node_id = node->getID(); // getUniqueID(node);

       // cout << " At node " << node_id << endl;

		if(visited.find(node_id)!=visited.end())
        {
		    if (node->getType() != DT_LIT)
            {
                    //cout <<  "Already visited node : " << node_id << "Returning " << endl;
                    return ;
            }
            else
            {
                int varNum = abs(node->getVal());
                if (!tseitinY[varNum])
                {
                   //// cout <<  "Already visited node : " << node_id << "Returning " << endl;
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

			string name = " ";

            if (!(activeY[varNum] || tseitinY[varNum]))  //input variable
            {
				name = getInputName(varNum);
				if(!polarity) {
					name = "DS_INP_NEG_"+to_string(varNum);
					ofs<<".subckt not neg1= "<< getInputName(varNum) <<" negOut= "<<name<<endl;
                    negXT.insert(varNum);
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
                    vector <int> dependents;
                    if (depCONST.count (varNum) != 0 || depCONST.count(-varNum) != 0) //Tseitin is a constant
                    {   
                    //  Polarity ?? 
		                if(visited.find(node_id)!=visited.end())
                           return;

                        if (depCONST.count(varNum) != 0)
                        {
					       // ofs<<".subckt equate equate1 on equateOut = " << getInputName(varNum)  <<endl;
				            name = getInputName(varNum);
                        }
                        else
                        {
					        //    ofs<<".subckt equate equate1 off equateOut = " << getInputName(varNum)  <<endl;
				                name = getInputNegName(varNum);
                //instead of varnum print DT_BOT
                        }
                        visited[node_id] = name;
                     }
                     else //Not a tseitin constant
                     {
                //Have we seen this tseitin with this assignment before? If so, reuse the variable
                        //cout << "varNum " << varNum << endl;
                        string tname = "T_" + to_string(varNum);
                        string constr_name = tname;
                        
                        if (leaves[varNum].size() > 0) 
                        {
                            //for (auto &ait : assign)
                             //   cout << "Assign " << ait;
                            //cout << endl;
                            for (auto & lit: leaves[varNum])
                            {
                                if (activeY[lit])
                                {
                                    if (assign.find(lit) != assign.end())
                                        constr_name  += "_on";
                                    else 
                                    {
                                         if (assign.find(-lit) != assign.end())
                                             constr_name  += "_off";
                                         else
                                         {
                                            cout << "Lit " << lit << " has no assignment " << endl;
                                            assert (false);
                                         }
                                    }
                                 }
                             }

                             string temp_var;
                             if (tseitin_visited.count (constr_name) > 0)
                             {
                                 //Reuse the same tseitin variable if the assignments are the same
                                visited[node_id] = tseitin_visited [constr_name]; 
                                return;
                             }
                             else 
                             {
                                    //Tseitin for the first time or different assignment
                                    ofs << ".subckt  " << tname;
                                    temp_var = getInputName(varNum) + "_" +  to_string(tnum) ;
                                    tseitin_visited[constr_name] = temp_var;

                                    for (auto & lit: leaves[varNum])
                                    {
                                        ofs << " " << tname << "_INP_" << lit << "="  ;
                                        if (activeY[lit])
                                        {
                                                if (assign.find (lit) != assign.end())
                                                    ofs << "on " ;
                                                else
                                                if (assign.find (-lit) != assign.end())
                                                    ofs << "off " ;
                                                else
                                                    assert (false);
                                        }
                                        else //X
                                        {
                                            ofs << getInputName(lit);

                                        }

                                    }

                                    visited[node_id] = temp_var;
                                    ofs << " " << tname << "_OUT="   <<  temp_var << endl;

                                    //print y_i \and sk_i \or \neg_yi \and \neg sk_i
                                    vector <string> c1;
                                    vector <string> c2;
                                    vector <string> c3;

                                    c1.push_back (getInputName(varNum));
                                    c1.push_back (temp_var); 
                                    writeOPtoBLIF_rec(c1, 0, ofs, temp_var+"_sk"); //Check what this should be -- not sure SS
                                    if (negXT.find (varNum) == negXT.end())
                                    {
                                        ofs<<".subckt not neg1="<< getInputName(varNum) <<" negOut=" << getInputNegName(varNum)<<endl;
                                        negXT.insert(varNum);
                                    }
                                    string neg_sk = "NEG_" +temp_var;
                                    ofs<<".subckt not neg1="<< temp_var <<" negOut=" << neg_sk <<endl;
                                    c2.push_back(getInputNegName(varNum));
                                    c2.push_back(neg_sk);
                                    writeOPtoBLIF_rec(c2, 0, ofs, "NEG_" + temp_var +"_sk"); //Check what this should be -- not sure SS
                                    c3.push_back(temp_var +"_sk");
                                    c3.push_back("NEG_" + temp_var +"_sk");
                                    writeOPtoBLIF_rec(c3, 1, ofs, temp_var +"_skwhole"); //Check what this should be -- not sure SS
                                    tnum ++;

                                }
                        }
                        else //Not a constant nor does it have leaves
                            assert (false);
                  
                  } //Not a tseitin constant ends
            } //Tseitin ends

          } //Not X ends
          //  cout << "Name for " << node_id << " is " << name << endl;
	    } //DT Lit ends
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
                if (it->getType () !=  DT_LIT)
                {
                    set <int> newassign = assign;
                    if (it->getType() == DT_AND)
                    {
                        writeDSharp_rec(it, ofs, visited, negXT, newassign, tnum, leaves, tseitin_visited, printT);
                        for (auto &t_it : printT)
                            children.push_back(t_it);
                        printT.resize(0);
                        children.push_back(visited[it->getID()] );

                    }
                    else
                    {
                        writeDSharp_rec(it, ofs, visited, negXT, newassign, tnum, leaves, tseitin_visited, printT);
                        children.push_back(visited[it->getID()] );
                    }
                }
                else
                {
                    writeDSharp_rec(it, ofs, visited, negXT, assign, tnum, leaves, tseitin_visited, printT);
                    assert (it->getType() == DT_LIT);
                    if (tseitinY[abs(it->getVal())]) //If Tseitin get appropriate name
                    {
                        bool polarity = it->getVal()>0?1:0;
                        int varNum = abs(it->getVal());
                        string constr_name = "T_" + to_string (varNum);
                        if (leaves[varNum].size() > 0)
                        {
                            if (leaves[varNum].size() == 1 && depCONST.find(varNum) != depCONST.end()) //It is a constant; 
                            {
                                    children.push_back(visited[it->getID()] );
                                    continue;
                            }

                            for (auto & lit: leaves[varNum])
                            {
                                if (activeY[lit])
                                {
                                    if (assign.find(lit) != assign.end())
                                    {
                                        constr_name  += "_on";
                                    }
                                    else 
                                    { 
                                        if (assign.find(-lit) != assign.end())
                                         constr_name  += "_off";
                                        else 
                                            assert (false);
                                    }
                                 }
                             }

                            //cout << "constr_name " << constr_name << endl;
                           assert (tseitin_visited.count (constr_name) > 0);

                         }
                         if (node->getType() == DT_AND)
                            children.push_back(visited[it->getID()] + "_skwhole");
                         else
                         {
                            printT.push_back(visited[it->getID()] + "_skwhole");
                            if (!polarity)
                            {
                                    string pol_name = "NEG_" + tseitin_visited[constr_name];
                                    //ofs << ".subckt not neg1 = " << tseitin_visited[constr_name] << " negOut = " <<  pol_name << endl;
                                    children.push_back( pol_name );

                            }
                            else
                                children.push_back(tseitin_visited [constr_name] );
                         }
                         //What if it is a constant?
                    }
                    else
				        children.push_back(visited[it->getID()] );
                }
          //      cout << "Adding child " <<  (*it)->getID() << " i.e.,  " <<  visited[(*it)->getID()] << " to children of " << node_id << endl;
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
		} //Else (Operator node) ends

	}
//}


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




                      /*
                            map < int, string> tvisited; //A visited map for tseitins at the subtree rooted at this main tseitin node
                            cout << "calling printTseitin for " << varNum << ". Leaves size " << leaves[varNum].size()<< endl;
                            tnum++;
                            if (visited.find(node_id) != visited.end () && leaves[varNum].size() <= 0 )    //Already visited and does not have activeY leaves
                                return;

                            visited[node_id] = printTseitin (ofs, tnum, varNum, assign, tvisited, polarity, negX); 
                     }
                     */
