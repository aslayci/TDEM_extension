#include "allocator.h"
#include "anyoption.h"
#include "iheap.h"
#include <ctime>

namespace _Cide{

    allocator::allocator(AnyOption* opt1) {

        opt = opt1;
        delim = " \t";

        sfmt_init_gen_rand(&sfmtSeed , 95082);

        n = strToInt(opt->getValue("n"));
        m = strToInt(opt->getValue("m"));
        k = strToInt(opt->getValue("k"));
        nrItems = strToInt(opt->getValue("nrItems"));
        kappa = strToInt(opt->getValue("attentionConstraint"));
        epsilon = strToDouble(opt->getValue("epsilon"));
        ell = strToDouble(opt->getValue("ell"));
        outFolderName = opt->getValue("outputFolder");

        nrPairs = n * nrItems;

        for(int i = 0; i < n; i++)
            graphT.push_back(vector<int>());

        delta = pow(double (1 / (double) n), ell);

        prevSize = 0;
        hyper_degree = std::vector<double>(nrPairs,0);
        for(int i = 0; i < nrPairs; i++)
            hyperG.push_back(std::vector<int>());

        rcList = new itemGraphList();
        //item-specific probT is aligned with graphT for each item
        for(int i = 0; i < nrItems; i++) {
            _Cide::itemGraph *ig = new _Cide::itemGraph(n);
            for (int i = 0; i < n; i++)
                ig->probT.push_back(std::vector< double>());
            rcList->push_back(ig);
        }
        nodeDegree = std::vector<double>(n,0.0);

        cout << "nr items " << nrItems << endl;
        cout << "attention bound " << kappa << endl;
        cout << "assignment size " << k << endl;

        readNodeLeaningsFile();
        readItemLeaningsFile();

        readTICGraph();
        cout << "successfully read everything " << endl;
        arrangeOutputFiles();
        cout << "starting assignment for tdem" << endl;
        tdem();

// comment out below to run the baselines
        degreeClose(theta, k);
        degreeFar(theta, k);
        degreeWeighted(theta, k);

    }

    double allocator::tdem() {

        cout << "computation for lower bounding OPT started " << endl;

        clock_t common_begin = clock();
        double lb = lowerBoundOPT();
        cout << "lower bound identified: " << lb << endl;

        theta = (32 + 16.0/3.0 * epsilon) * n * (log(n) + log(2) +  logcnk(nrPairs,k)) / (epsilon * epsilon * lb);

        cout << "final sample size " << theta << endl;
        generateRCSets(theta);
        cout << "generated RC sets" << endl;
        clock_t common_end = clock();
        duration_common = double(common_end - common_begin) / CLOCKS_PER_SEC;

        double greedySolution = n * rcGreedy(theta, k, true);
        cout << "computed TDEM" << endl;
        return greedySolution;
    }


    double allocator::lowerBoundOPT() {

        double epsilon_1 = epsilon;

        for (int x = 1; x < log2(n); x++) {
//            cout << "here x = " << x << endl;

            int64 theta_x = (4+(16.0/3.0) * epsilon_1)* (log(n) + logcnk(nrPairs,k) + log(log2(n) + 1)) * pow(2.0,x) / (2.0 * epsilon_1 * epsilon_1);
//            cout << "here theta_x " << theta_x << endl;
            generateRCSets(theta_x);
            double ept = rcGreedy(theta_x, k, false);
//            cout << "ept " << ept << endl;

            if (ept > ((1+epsilon_1) * 2.0 / pow(2.0, x))) {
                double lowerBound = ept * n / (1 + epsilon_1);
                return lowerBound;
            }
        }
        cout << "returning naive lower bound  " << endl;
        double naive = (double) k * 2.0;
        return naive;

    }


    void allocator::generateRCSets(int64 newSize) {

        // sample target nodes
        for (int i = prevSize; i < newSize; i++) {
            int randTarget = sfmt_genrand_uint32(&sfmtSeed) % n;
            targetNodes.push_back(randTarget);
        }

        // expand coordinated RR sets samples of items
        for(int itemID = 0; itemID < nrItems; itemID++) {
            rcList->at(itemID)->generateRRSample(targetNodes, prevSize, newSize);
        }

        for(int itemID = 0; itemID < nrItems; itemID++) {
            for (int rcID = prevSize; rcID < newSize; rcID++) {
                int target = targetNodes[rcID];
                for (int j = 0; j < rcList->at(itemID)->hyperGT[rcID].size(); j++) {
                    int t = rcList->at(itemID)->hyperGT[rcID][j];
                    int t_p = t + n * itemID;
                    hyperG[t_p].push_back(rcID);
                    double a,b;
                    if (nodeLeanings[target] < itemLeanings[itemID] ){
                      a=nodeLeanings[target];
                      b=itemLeanings[itemID];
                    }
                    else{
                      b=nodeLeanings[target];
                      a=itemLeanings[itemID];
                    }
                    hyper_degree[t_p]+= 2- 2*a - a*a - b*b + 2*b;
//                    hyper_degree[t_p] += std::abs(nodeLeanings[target] - itemLeanings[itemID]);
                }
            }
        }
        prevSize = newSize;

    }

    double allocator::rcGreedy(int64 rcSampleSize, int k, bool extraResults) {

        clock_t begin = clock();
        priority_queue<pair<int, double>, vector<pair<int, double>>, CompareBySecond>heap;
        std::vector<double> divExpScore(nrPairs, 0);
        std::vector<int> attentionQuota = std::vector<int>(n,kappa);

//        std::vector<double> rcMinSeen(rcSampleSize,-5.0);
//        std::vector<double> rcMaxSeen(rcSampleSize, 5.0);

        std::vector<set<double>> rcSeen(rcSampleSize);


        vector<bool> isCovered(rcSampleSize, false);
        vector<bool> pairMark(nrPairs, true);


        double totalExpScore = 0;
        int bestPairID, bestNodeID, bestItemID;

        for (int i = 0; i < nrPairs; i++) {
            std::pair<int, double>pairVal(std::make_pair(i, hyper_degree[i]));
            heap.push(pairVal);
            divExpScore[i] = hyper_degree[i];
        }

        int nrCoveredRC = 0;
        seedSet.clear();

        cout << "about to go into while loop" << endl;
        while ((int)seedSet.size() < k) {

            pair<int, double> pairVal = heap.top();
            heap.pop();
            bestPairID = pairVal.first;
            bestNodeID = (int) bestPairID % n;
            // if the attention quota for this node is filled, remove it from queue and contimue
            if(attentionQuota[bestNodeID] == 0)
                continue;
            // if its marginal gain in the previous pair selection iteration, update its mg in the queue
            if (pairVal.second != divExpScore[pairVal.first]) {
                pairVal.second = divExpScore[pairVal.first];
                heap.push(pairVal);
                continue;
            }

            bestItemID = (int) bestPairID / n;
            totalExpScore += divExpScore[bestPairID];
            seedSet.push_back(bestPairID);
            seedScores.push_back(n * divExpScore[bestPairID] / (double) rcSampleSize);
            pairMark[bestPairID] = false;
            attentionQuota[bestNodeID]--;


            // update the hyper_degree of the pairs whose marginal gain change due to the best pair selection
            vector<int> rcsAffected = hyperG[bestPairID]; // ids of RC sets that contain this best pair
            for (int j = 0; j < rcsAffected.size(); j++) {
                int rcID = rcsAffected[j];
                int target = targetNodes[rcID];

                if ( rcID > rcSampleSize){
                  cout << "error. I reached an rcID larger than the number of RC sets" << endl;
                }
//                double prevGain, currGain;
      //          cout << "about to enter if" << endl ;
                if (!isCovered[rcID]) {
      //              cout<<"before making true" << endl;
                    isCovered[rcID] = true;
                    nrCoveredRC++;
//                    cout << "ID: " << rcID << endl;
//                    cout << "rcSeen size: " << rcSeen.size() << endl;

    //                cout <<"before inserting -1.0" << endl;
                    try{
                    rcSeen[rcID].insert(-1.0);
                  }
                  catch (...){
                    cout << "caught exception while trying to insert -1.0" << endl;
                    cout << "rcID: " << rcID << endl;
                  }
    //                cout <<"inserted -1.0" << endl;
    //                cout <<"before inserting the target: " << nodeLeanings[target] << endl;
                  try{
                    rcSeen[rcID].insert(nodeLeanings[target]);
                  }
                  catch (...){
                    cout << "caught exception while trying to insert node leaning" << endl;
                    cout << "rcID: " << rcID << endl;
                    cout << "nodeLeanings[target]: " << nodeLeanings[target] << endl;
                  }
    //                cout <<"before inserting 1.0" << endl;
                    try{
                    rcSeen[rcID].insert(1.0);
                    }
                    catch (...){
                      cout << "caught exception while trying to insert 1.0" << endl;
                      cout << "rcID: " << rcID << endl;
                    }


    //                cout << "rcSeen[rcID] size after: " << sizeof(rcSeen[rcID]) << endl;
                }
    //            cout << "after if" << endl ;
                //New diversity function implementation
                rcSeen[rcID].insert(itemLeanings[bestItemID]);
                double a,b;
                a=double(*(std::prev(rcSeen[rcID].find(itemLeanings[bestItemID]))));
                b=double(*(std::next(rcSeen[rcID].find(itemLeanings[bestItemID]))));

                  // compute the amount of change in marginal gain for each item contained in this RC set
                  for(int itemID = 0; itemID < nrItems; itemID++) {
                    if (itemLeanings[itemID] <= a  || itemLeanings[itemID] >= b ){
                      continue;
                    }
                    double prev_quad, new_quad;
                    if(itemLeanings[itemID] < itemLeanings[bestItemID]){
                      prev_quad=(itemLeanings[itemID]-b)*(itemLeanings[itemID]-b);
                      new_quad=(itemLeanings[itemID]-itemLeanings[bestItemID])*(itemLeanings[itemID]-itemLeanings[bestItemID])+(itemLeanings[bestItemID]-b)*(itemLeanings[bestItemID]-b);
                    }
                    else{
                      prev_quad=(a-itemLeanings[itemID])*(a-itemLeanings[itemID]);
                      new_quad=(a-itemLeanings[bestItemID])*(a-itemLeanings[bestItemID])+(itemLeanings[bestItemID]-itemLeanings[itemID])*(itemLeanings[bestItemID]-itemLeanings[itemID]);
                    }
                    vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                    for (int z = 0; z < rrTemp.size(); z++) {
                        int pairID = rrTemp[z] + n * itemID;
                        if(pairMark[pairID]) {
                            double tempD = divExpScore[pairID];
                            divExpScore[pairID] = tempD-new_quad+prev_quad;
                            if(divExpScore[pairID] < 0) {
                                divExpScore[pairID] = 0;
                            }

                        }
                    }
                  }


/*
                // if it is the first time this RC is covered by a seed pair -- below the marginal gain update operations for this case
                if (!isCovered[rcID]) {
                    isCovered[rcID] = true;
                    nrCoveredRC++;
                    rcMinSeen[rcID] = std::min(nodeLeanings[target], itemLeanings[bestItemID]);
                    rcMaxSeen[rcID] = std::max(nodeLeanings[target], itemLeanings[bestItemID]);

                    // compute the amount of change in marginal gain for each item contain in this RC set
                    for(int itemID = 0; itemID < nrItems; itemID++) {

                        prevGain = std::abs(nodeLeanings[target] - itemLeanings[itemID]); // mg to empty set
                        if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                            currGain = 0;
                        }
                        else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                            currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                            currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                        }
                        vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                        for (int z = 0; z < rrTemp.size(); z++) {
                            int pairID = rrTemp[z] + n * itemID;
                            if(pairMark[pairID]) {
                                double tempD = divExpScore[pairID];
                                divExpScore[pairID] = tempD - prevGain + currGain;
                                if(divExpScore[pairID] < 0) {
                                    divExpScore[pairID] = 0;
                                }

                            }
                        }
                    }
                }

                // if it was already covered before
                else {
                    if(itemLeanings[bestItemID] >= rcMinSeen[rcID] && itemLeanings[bestItemID] <= rcMaxSeen[rcID])
                        continue;

                    double prevMin = rcMinSeen[rcID];
                    double prevMax = rcMaxSeen[rcID];
                    rcMinSeen[rcID] = std::min(prevMin, itemLeanings[bestItemID]);
                    rcMaxSeen[rcID] = std::max(prevMax, itemLeanings[bestItemID]);

                    for(int itemID = 0; itemID < nrItems; itemID++) {
                        if (itemLeanings[itemID] >= prevMin &&  itemLeanings[itemID] <= prevMax) {
                            prevGain = 0;
                        }
                        else if(itemLeanings[itemID] < prevMin) {
                            prevGain = prevMin - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > prevMax) {
                            prevGain = itemLeanings[itemID] - prevMax;
                        }

                        if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                            currGain = 0;
                        }
                        else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                            currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                            currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                        }

                        vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                            for (int z = 0; z < rrTemp.size(); z++) {
                                int pairID = rrTemp[z] + n * itemID;
                                if(pairMark[pairID]) {
                                    double tempD = divExpScore[pairID];
                                    divExpScore[pairID] = tempD - prevGain + currGain;
                                    if(divExpScore[pairID] < 0) {
                                        divExpScore[pairID] = 0;
                                    }

                                }
                            }
                        }
                } // end-if this RC was already covered before
*/
            }// end of for loop for affected
        } // end of while k loop


        ///////////// produce the additional results here
        if(extraResults) {

            clock_t end = clock();
            totalDuration = (double(end - begin) / CLOCKS_PER_SEC) + duration_common; // in seconds
            totalMemory = getCurrentMemoryUsage(); // in MB

            cout << "total tdem time taken (in seconds) " << totalDuration << " total memory (in mb) " << totalMemory << endl;

            double totMGs = 0;
            for (int i = 0; i < seedSet.size(); i++) {
                int node = (int) seedSet[i] % n;
                int item = (int) seedSet[i] / n;
                totMGs += seedScores[i];
                writeInMasterOutputFile(node,item,seedScores[i],totMGs,totalDuration,totalMemory);
            }
            cout << "total tdem div. exp. score " << totMGs << endl;

            // compute for each seed pair its prob. of reaching target nodes

            string extraFName1 = outFolderName + OS_SEP + "pairReachProbs_tdem.txt";
            ofstream extraStream1;

            if(extraStream1.is_open())
                extraStream1.close();

            extraStream1.open(extraFName1.c_str());

            if (extraStream1.is_open() == false) {
                cout << "Can't open file " << extraFName1  << " for writing" << endl;
                exit(1);
            }

            extraStream1 << "nodeID" << " " << "itemID" << " " <<  "targetNodeID" << " " << "reachProb" << endl;

            extraStream1 << std::fixed;
            extraStream1.precision(8);

            vector< vector<double> > pairNodeReachProbs;

            for (int i = 0; i < k; i++) {
                pairNodeReachProbs.push_back(std::vector<double>(n,0.0));
            }

            for (int i = 0; i < k; i++) {
                int seedPairID = seedSet[i];
                vector<int> rcsCovered = hyperG[seedPairID]; // ids of RC sets that contain this best pair
                for (int j = 0; j < rcsCovered.size(); j++) {
                    int rcID = rcsCovered[j];
                    int target = targetNodes[rcID];
                    double tempVal = pairNodeReachProbs[i][target];
                    pairNodeReachProbs[i][target] = tempVal + 1.0;
                }
            }

            for (int i = 0; i < k; i++) {
                int seedPairID = seedSet[i];
                int nodeID = (int) seedPairID % n;
                int itemID = (int) seedPairID / n;
                for (int j = 0; j < n; j++) {
                    double tempVal = pairNodeReachProbs[i][j];
                    pairNodeReachProbs[i][j] = (double) n * tempVal / (double) rcSampleSize;
                    extraStream1 << nodeID << " " << itemID << " " <<  j << " " << pairNodeReachProbs[i][j] << endl;
                }
            }

            extraStream1.close();

            // compute fv(seedset) for each target node v
            string extraFName2 = outFolderName + OS_SEP + "nodeExpLevels_tdem.txt";
            ofstream extraStream2;

            if(extraStream2.is_open())
                extraStream2.close();

            extraStream2.open(extraFName2.c_str());

            if (extraStream2.is_open() == false) {
                cout << "Can't open file " << extraFName2  << " for writing" << endl;
                exit(1);
            }

            extraStream2 << "targetNodeID" << " " << "exposure_level" << endl;
            vector<double> nodeExpLevels(n,0.0);

            for (int rcID = 0; rcID < rcSampleSize; rcID++) {
                int target = targetNodes[rcID];
                if(isCovered[rcID]) {
                  for (std::set<double>::iterator it = rcSeen[rcID].begin() ; it != std::prev(rcSeen[rcID].end()); ++it){
                   double a=*it;
                   double b=*(std::next(it));
                    nodeExpLevels[target] += (a-b)*(a-b);
                  }
                }
            }

//            double kontrolAw = 0;
            for (int i = 0 ; i < n ; i++) {
                double tempVal = nodeExpLevels[i];
                nodeExpLevels[i] = (double) n * tempVal / (double) rcSampleSize;
//                kontrolAw += nodeExpLevels[i];
                extraStream2 << i << " " << nodeExpLevels[i] << endl;
            }

            extraStream2.close();
//            cout << "kontrol " << kontrolAw << endl;

        } // end of extra results

        return totalExpScore / (double) rcSampleSize;
    }

    double allocator::degreeClose(int64 rcSampleSize, int k) {
        clock_t begin = clock();

        priority_queue<pair<int, double>, vector<pair<int, double>>, CompareBySecond>heap;
        std::vector<double> divExpScore(nrPairs, 0);
        std::vector<int> attentionQuota = std::vector<int>(n,kappa);

//        std::vector<double> rcMinSeen(rcSampleSize,-5.0);
//        std::vector<double> rcMaxSeen(rcSampleSize, 5.0);

        std::vector<set<double>> rcSeen(rcSampleSize);


        vector<bool> isCovered(rcSampleSize, false);
        vector<bool> pairMark(nrPairs, true);

        double totalExpScore = 0;
        int bestPairID, bestNodeID, bestItemID;

        divExpScore = hyper_degree;

        for (int i = 0; i < n; i++) {
            double val = (double) nodeDegree[i];
            std::pair<int, double>pairVal(std::make_pair(i, val));
            heap.push(pairVal);
        }
        seedSet.clear();
        seedScores.clear();

        while ((int)seedSet.size() < k) {

            pair<int, double> pairVal = heap.top();
            bestNodeID = pairVal.first;
            attentionQuota[bestNodeID]--;

            if(attentionQuota[bestNodeID] == 0) { //if the attention quota for this node is topped already, pop it from the queue forevah
                heap.pop();
            }

            double itMax = 2.0;
            bestItemID=0;
            for (int itemID = 0; itemID < nrItems; itemID++) {
                int pairIDtemp = bestNodeID + n * itemID;
                if (pairMark[pairIDtemp]) { // if this item is not assigned to this node yet
                  //variance
                    if(itMax > (nodeLeanings[bestNodeID] - itemLeanings[itemID])*(nodeLeanings[bestNodeID] - itemLeanings[itemID]) ) {
                        itMax = (nodeLeanings[bestNodeID] - itemLeanings[itemID])*(nodeLeanings[bestNodeID] - itemLeanings[itemID]);
                        bestItemID = itemID;
                    }
                }
            }

            bestPairID = bestNodeID + n * bestItemID;
            totalExpScore += divExpScore[bestPairID];
            seedSet.push_back(bestPairID);
            seedScores.push_back(n * divExpScore[bestPairID] / (double) rcSampleSize);
            pairMark[bestPairID] = false;

            // update the hyper_degree of the pairs whose marginal gain change due to the best pair selection
            vector<int> rcsAffected = hyperG[bestPairID]; // ids of RC sets that contain this best pair
            for (int j = 0; j < rcsAffected.size(); j++) {
                int rcID = rcsAffected[j];
                int target = targetNodes[rcID];
//                double prevGain, currGain;

                // if it is the first time this RC is covered by a seed pair -- below the marginal gain update operations for this case
                if (!isCovered[rcID]) {
                    isCovered[rcID] = true;
  //                  rcMinSeen[rcID] = std::min(nodeLeanings[target], itemLeanings[bestItemID]);
  //                  rcMaxSeen[rcID] = std::max(nodeLeanings[target], itemLeanings[bestItemID]);
                    rcSeen[rcID].insert(-1.0);
                    rcSeen[rcID].insert(nodeLeanings[target]);
                    rcSeen[rcID].insert(1.0);

                  }

                  //New diversity function implementation
                  rcSeen[rcID].insert(itemLeanings[bestItemID]);
                  double a,b;
                  a=double(*(std::prev(rcSeen[rcID].find(itemLeanings[bestItemID]))));
                  b=double(*(std::next(rcSeen[rcID].find(itemLeanings[bestItemID]))));

                    // compute the amount of change in marginal gain for each item contained in this RC set
                    for(int itemID = 0; itemID < nrItems; itemID++) {
                      if (itemLeanings[itemID] <= a  || itemLeanings[itemID] >= b ){
                        continue;
                      }
                      double prev_quad, new_quad;
                      if(itemLeanings[itemID] < itemLeanings[bestItemID]){
                        prev_quad=(itemLeanings[itemID]-b)*(itemLeanings[itemID]-b);
                        new_quad=(itemLeanings[itemID]-itemLeanings[bestItemID])*(itemLeanings[itemID]-itemLeanings[bestItemID])+(itemLeanings[bestItemID]-b)*(itemLeanings[bestItemID]-b);
                      }
                      else{
                        prev_quad=(a-itemLeanings[itemID])*(a-itemLeanings[itemID]);
                        new_quad=(a-itemLeanings[bestItemID])*(a-itemLeanings[bestItemID])+(itemLeanings[bestItemID]-itemLeanings[itemID])*(itemLeanings[bestItemID]-itemLeanings[itemID]);
                      }
                      vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                      for (int z = 0; z < rrTemp.size(); z++) {
                          int pairID = rrTemp[z] + n * itemID;
                          if(pairMark[pairID]) {
                              double tempD = divExpScore[pairID];
                              divExpScore[pairID] = tempD-new_quad+prev_quad;
                              if(divExpScore[pairID] < 0) {
                                  divExpScore[pairID] = 0;
                              }

                          }
                      }
                  }


/*
                    // compute the amount of change in marginal gain for each item contain in this RC set
                    for(int itemID = 0; itemID < nrItems; itemID++) {

                        prevGain = std::abs(nodeLeanings[target] - itemLeanings[itemID]); // mg to empty set
                        if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                            currGain = 0;
                        }
                        else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                            currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                            currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                        }
                        vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                        for (int z = 0; z < rrTemp.size(); z++) {
                            int pairID = rrTemp[z] + n * itemID;
                            if(pairMark[pairID]) {
                                double tempD = divExpScore[pairID];
                                divExpScore[pairID] = tempD - prevGain + currGain;
                                if(divExpScore[pairID] < 0) {
                                    divExpScore[pairID] = 0;
                                }
                            }
                        }
                    }
                }

                // if it was already covered before
                else {
                    if(itemLeanings[bestItemID] >= rcMinSeen[rcID] && itemLeanings[bestItemID] <= rcMaxSeen[rcID])
                        continue;

                    double prevMin = rcMinSeen[rcID];
                    double prevMax = rcMaxSeen[rcID];
                    rcMinSeen[rcID] = std::min(prevMin, itemLeanings[bestItemID]);
                    rcMaxSeen[rcID] = std::max(prevMax, itemLeanings[bestItemID]);

                    for(int itemID = 0; itemID < nrItems; itemID++) {
                        if (itemLeanings[itemID] >= prevMin &&  itemLeanings[itemID] <= prevMax) {
                            prevGain = 0;
                        }
                        else if(itemLeanings[itemID] < prevMin) {
                            prevGain = prevMin - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > prevMax) {
                            prevGain = itemLeanings[itemID] - prevMax;
                        }

                        if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                            currGain = 0;
                        }
                        else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                            currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                            currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                        }

                        vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                        for (int z = 0; z < rrTemp.size(); z++) {
                            int pairID = rrTemp[z] + n * itemID;
                            if(pairMark[pairID]) {
                                double tempD = divExpScore[pairID];
                                divExpScore[pairID] = tempD - prevGain + currGain;
                                if(divExpScore[pairID] < 0) {
                                    divExpScore[pairID] = 0;
                                }
                            }
                        }
                    }
                } // end-if this RC was already covered before
*/

            }// end of for loop for affected
        } // end of while k loop



        clock_t end = clock();
        totalDuration = (double(end - begin) / CLOCKS_PER_SEC) + duration_common; // in seconds
        totalMemory = getCurrentMemoryUsage(); // in MB

        cout << "total degree-minvar time taken (in seconds) " << totalDuration << " total memory (in mb) " << totalMemory << endl;

        string extraFName0 = outFolderName + OS_SEP + "assignment_degreeClose.txt";
        ofstream extraStream0;
        if(extraStream0.is_open())
            extraStream0.close();

        extraStream0.open(extraFName0.c_str());

        if (extraStream0.is_open() == false) {
            cout << "Can't open file " << extraFName0  << " for writing" << endl;
            exit(1);
        }

        extraStream0 << "nodeID" << " " << "itemID" << " " <<  "mgScore" << " " << "cumScore" << " " << "duration(sec)" << " " << "memory(mb)" << endl;
        double totMGs = 0;
        for (int i = 0; i < seedSet.size(); i++) {
            int node = (int) seedSet[i] % n;
            int item = (int) seedSet[i] / n;
            totMGs += seedScores[i];
            extraStream0 << node << " " << item << " " << seedScores[i] << " " << totMGs << " " << totalDuration << " " << totalMemory << endl;
        }
        cout << "total degree-minvar div. exp. score " << totMGs << endl;

        extraStream0.close();

        string extraFName1 = outFolderName + OS_SEP + "pairReachProbs_degreeClose.txt";
        ofstream extraStream1;

        if(extraStream1.is_open())
            extraStream1.close();

        extraStream1.open(extraFName1.c_str());

        if (extraStream1.is_open() == false) {
            cout << "Can't open file " << extraFName1  << " for writing" << endl;
            exit(1);
        }

        extraStream1 << "nodeID" << " " << "itemID" << " " <<  "targetNodeID" << " " << "reachProb" << endl;

        extraStream1 << std::fixed;
        extraStream1.precision(8);

        vector< vector<double> > pairNodeReachProbs;

        for (int i = 0; i < k; i++) {
            pairNodeReachProbs.push_back(std::vector<double>(n,0.0));
        }

        for (int i = 0; i < k; i++) {
            int seedPairID = seedSet[i];
            vector<int> rcsCovered = hyperG[seedPairID]; // ids of RC sets that contain this best pair
            for (int j = 0; j < rcsCovered.size(); j++) {
                int rcID = rcsCovered[j];
                int target = targetNodes[rcID];
                double tempVal = pairNodeReachProbs[i][target];
                pairNodeReachProbs[i][target] = tempVal + 1.0;
            }
        }

        for (int i = 0; i < k; i++) {
            int seedPairID = seedSet[i];
            int nodeID = (int) seedPairID % n;
            int itemID = (int) seedPairID / n;
            for (int j = 0; j < n; j++) {
                double tempVal = pairNodeReachProbs[i][j];
                pairNodeReachProbs[i][j] = (double) n * tempVal / (double) rcSampleSize;
                extraStream1 << nodeID << " " << itemID << " " <<  j << " " << pairNodeReachProbs[i][j] << endl;
            }
        }

        extraStream1.close();

        // compute fv(seedset) for each target node v
        string extraFName2 = outFolderName + OS_SEP + "nodeExpLevels_degreeClose.txt";
        ofstream extraStream2;

        if(extraStream2.is_open())
            extraStream2.close();

        extraStream2.open(extraFName2.c_str());

        if (extraStream2.is_open() == false) {
            cout << "Can't open file " << extraFName2  << " for writing" << endl;
            exit(1);
        }

        extraStream2 << "targetNodeID" << " " << "exposure_level" << endl;
        vector<double> nodeExpLevels(n,0.0);

        for (int rcID = 0; rcID < rcSampleSize; rcID++) {
            int target = targetNodes[rcID];
            if(isCovered[rcID]) {
              for (std::set<double>::iterator it = rcSeen[rcID].begin() ; it != std::prev(rcSeen[rcID].end()); ++it){
               double a=*it;
               double b=*(std::next(it));
                nodeExpLevels[target] += (a-b)*(a-b);
              }
            }
        }

        for (int i = 0 ; i < n ; i++) {
            double tempVal = nodeExpLevels[i];
            nodeExpLevels[i] = (double) n * tempVal / (double) rcSampleSize;
            extraStream2 << i << " " << nodeExpLevels[i] << endl;
        }

        extraStream2.close();

        return totalExpScore / (double) rcSampleSize;
    }

    double allocator::degreeFar(int64 rcSampleSize, int k) {

        clock_t begin = clock();

        priority_queue<pair<int, double>, vector<pair<int, double>>, CompareBySecond>heap;
        std::vector<double> divExpScore(nrPairs, 0);
        std::vector<int> attentionQuota = std::vector<int>(n,kappa);

//        std::vector<double> rcMinSeen(rcSampleSize,-5.0);
//        std::vector<double> rcMaxSeen(rcSampleSize, 5.0);

        std::vector<set<double>> rcSeen(rcSampleSize);


        vector<bool> isCovered(rcSampleSize, false);
        vector<bool> pairMark(nrPairs, true);

        double totalExpScore = 0;
        int bestPairID, bestNodeID, bestItemID;


        divExpScore = hyper_degree;

        for (int i = 0; i < n; i++) {
            double val = (double) nodeDegree[i];
            std::pair<int, double>pairVal(std::make_pair(i, val));
            heap.push(pairVal);
        }

        seedSet.clear();
        seedScores.clear();

        while ((int)seedSet.size() < k) {

            pair<int, double> pairVal = heap.top();
            bestNodeID = pairVal.first;
            attentionQuota[bestNodeID]--;

            if(attentionQuota[bestNodeID] == 0) { //if the attention quota for this node is topped already, pop it from the queue forevah
                heap.pop();
            }

            double itMax = 0;
            bestItemID=0;
            for (int itemID = 0; itemID < nrItems; itemID++) {
                int pairIDtemp = bestNodeID + n * itemID;
                if (pairMark[pairIDtemp]) { // if this item is not assigned to this node yet
                    if(itMax < (nodeLeanings[bestNodeID] - itemLeanings[itemID])*(nodeLeanings[bestNodeID] - itemLeanings[itemID]) ) {
                        itMax = (nodeLeanings[bestNodeID] - itemLeanings[itemID])*(nodeLeanings[bestNodeID] - itemLeanings[itemID]);
                        bestItemID = itemID;
                    }
                }
            }

            bestPairID = bestNodeID + n * bestItemID;
            totalExpScore += divExpScore[bestPairID];
            seedSet.push_back(bestPairID);
            seedScores.push_back(n * divExpScore[bestPairID] / (double) rcSampleSize);
            pairMark[bestPairID] = false;

            // update the hyper_degree of the pairs whose marginal gain change due to the best pair selection
            vector<int> rcsAffected = hyperG[bestPairID]; // ids of RC sets that contain this best pair
            for (int j = 0; j < rcsAffected.size(); j++) {
                int rcID = rcsAffected[j];
                int target = targetNodes[rcID];

                // if it is the first time this RC is covered by a seed pair -- below the marginal gain update operations for this case
                if (!isCovered[rcID]) {
                    isCovered[rcID] = true;
//                    rcMinSeen[rcID] = std::min(nodeLeanings[target], itemLeanings[bestItemID]);
//                    rcMaxSeen[rcID] = std::max(nodeLeanings[target], itemLeanings[bestItemID]);
                    rcSeen[rcID].insert(-1.0);
                    rcSeen[rcID].insert(nodeLeanings[target]);
                    rcSeen[rcID].insert(1.0);
                    }

                    //New diversity function implementation
                    rcSeen[rcID].insert(itemLeanings[bestItemID]);
                    double a,b;
                    a=double(*(std::prev(rcSeen[rcID].find(itemLeanings[bestItemID]))));
                    b=double(*(std::next(rcSeen[rcID].find(itemLeanings[bestItemID]))));

                      // compute the amount of change in marginal gain for each item contained in this RC set
                      for(int itemID = 0; itemID < nrItems; itemID++) {
                        if (itemLeanings[itemID] <= a  || itemLeanings[itemID] >= b ){
                          continue;
                        }
                        double prev_quad, new_quad;
                        if(itemLeanings[itemID] < itemLeanings[bestItemID]){
                          prev_quad=(itemLeanings[itemID]-b)*(itemLeanings[itemID]-b);
                          new_quad=(itemLeanings[itemID]-itemLeanings[bestItemID])*(itemLeanings[itemID]-itemLeanings[bestItemID])+(itemLeanings[bestItemID]-b)*(itemLeanings[bestItemID]-b);
                        }
                        else{
                          prev_quad=(a-itemLeanings[itemID])*(a-itemLeanings[itemID]);
                          new_quad=(a-itemLeanings[bestItemID])*(a-itemLeanings[bestItemID])+(itemLeanings[bestItemID]-itemLeanings[itemID])*(itemLeanings[bestItemID]-itemLeanings[itemID]);
                        }
                      vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                      for (int z = 0; z < rrTemp.size(); z++) {
                          int pairID = rrTemp[z] + n * itemID;
                          if(pairMark[pairID]) {
                              double tempD = divExpScore[pairID];
                              divExpScore[pairID] = tempD-new_quad+prev_quad;
                              if(divExpScore[pairID] < 0) {
                                  divExpScore[pairID] = 0;
                              }

                          }
                      }
                   }
/*
                    // compute the amount of change in marginal gain for each item contain in this RC set
                    for(int itemID = 0; itemID < nrItems; itemID++) {

                        prevGain = std::abs(nodeLeanings[target] - itemLeanings[itemID]); // mg to empty set
                        if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                            currGain = 0;
                        }
                        else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                            currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                            currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                        }
                        vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                        for (int z = 0; z < rrTemp.size(); z++) {
                            int pairID = rrTemp[z] + n * itemID;
                            if(pairMark[pairID]) {
                                double tempD = divExpScore[pairID];
                                divExpScore[pairID] = tempD - prevGain + currGain;
                                if(divExpScore[pairID] < 0) {
                                    divExpScore[pairID] = 0;
                                }
                            }//
                        }
                    }
                }

                // if it was already covered before
                else {
                    if(itemLeanings[bestItemID] >= rcMinSeen[rcID] && itemLeanings[bestItemID] <= rcMaxSeen[rcID])
                        continue;

                    double prevMin = rcMinSeen[rcID];
                    double prevMax = rcMaxSeen[rcID];
                    rcMinSeen[rcID] = std::min(prevMin, itemLeanings[bestItemID]);
                    rcMaxSeen[rcID] = std::max(prevMax, itemLeanings[bestItemID]);

                    for(int itemID = 0; itemID < nrItems; itemID++) {
                        if (itemLeanings[itemID] >= prevMin &&  itemLeanings[itemID] <= prevMax) {
                            prevGain = 0;
                        }
                        else if(itemLeanings[itemID] < prevMin) {
                            prevGain = prevMin - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > prevMax) {
                            prevGain = itemLeanings[itemID] - prevMax;
                        }

                        if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                            currGain = 0;
                        }
                        else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                            currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                            currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                        }

                        vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                        for (int z = 0; z < rrTemp.size(); z++) {
                            int pairID = rrTemp[z] + n * itemID;
                            if(pairMark[pairID]) {
                                double tempD = divExpScore[pairID];
                                divExpScore[pairID] = tempD - prevGain + currGain;
                                if(divExpScore[pairID] < 0) {
                                    divExpScore[pairID] = 0;
                                }
                            }
                        }
                    }
                } // end-if this RC was already covered before
*/
            }// end of for loop for affected
        } // end of while k loop

        clock_t end = clock();
        totalDuration = (double(end - begin) / CLOCKS_PER_SEC) + duration_common; // in seconds
        totalMemory = getCurrentMemoryUsage(); // in MB

        cout << "total degree-maxvar time taken (in seconds) " << totalDuration << " total memory (in mb) " << totalMemory << endl;

        string extraFName0 = outFolderName + OS_SEP + "assignment_degreeFar.txt";
        ofstream extraStream0;
        if(extraStream0.is_open())
            extraStream0.close();

        extraStream0.open(extraFName0.c_str());

        if (extraStream0.is_open() == false) {
            cout << "Can't open file " << extraFName0  << " for writing" << endl;
            exit(1);
        }

        extraStream0 << "nodeID" << " " << "itemID" << " " <<  "mgScore" << " " << "cumScore" << " " << "duration(sec)" << " " << "memory(mb)" << endl;
        double totMGs = 0;
        for (int i = 0; i < seedSet.size(); i++) {
            int node = (int) seedSet[i] % n;
            int item = (int) seedSet[i] / n;
            totMGs += seedScores[i];
            extraStream0 << node << " " << item << " " << seedScores[i] << " " << totMGs << " " << totalDuration << " " << totalMemory << endl;
        }
        cout << "total degree-maxvar div. exp. score " << totMGs << endl;
        extraStream0.close();


        // compute for each seed pair its prob. of reaching target nodes

        string extraFName1 = outFolderName + OS_SEP + "pairReachProbs_degreeFar.txt";
        ofstream extraStream1;

        if(extraStream1.is_open())
            extraStream1.close();

        extraStream1.open(extraFName1.c_str());

        if (extraStream1.is_open() == false) {
            cout << "Can't open file " << extraFName1  << " for writing" << endl;
            exit(1);
        }

        extraStream1 << "nodeID" << " " << "itemID" << " " <<  "targetNodeID" << " " << "reachProb" << endl;

        extraStream1 << std::fixed;
        extraStream1.precision(8);

        vector< vector<double> > pairNodeReachProbs;

        for (int i = 0; i < k; i++) {
            pairNodeReachProbs.push_back(std::vector<double>(n,0.0));
        }

        for (int i = 0; i < k; i++) {
            int seedPairID = seedSet[i];
            vector<int> rcsCovered = hyperG[seedPairID]; // ids of RC sets that contain this best pair
            for (int j = 0; j < rcsCovered.size(); j++) {
                int rcID = rcsCovered[j];
                int target = targetNodes[rcID];
                double tempVal = pairNodeReachProbs[i][target];
                pairNodeReachProbs[i][target] = tempVal + 1.0;
            }
        }

        for (int i = 0; i < k; i++) {
            int seedPairID = seedSet[i];
            int nodeID = (int) seedPairID % n;
            int itemID = (int) seedPairID / n;
            for (int j = 0; j < n; j++) {
                double tempVal = pairNodeReachProbs[i][j];
                pairNodeReachProbs[i][j] = (double) n * tempVal / (double) rcSampleSize;
                extraStream1 << nodeID << " " << itemID << " " <<  j << " " << pairNodeReachProbs[i][j] << endl;
            }
        }

        extraStream1.close();

        // compute fv(seedset) for each target node v
        string extraFName2 = outFolderName + OS_SEP + "nodeExpLevels_degreeFar.txt";
        ofstream extraStream2;

        if(extraStream2.is_open())
            extraStream2.close();

        extraStream2.open(extraFName2.c_str());

        if (extraStream2.is_open() == false) {
            cout << "Can't open file " << extraFName2  << " for writing" << endl;
            exit(1);
        }

        extraStream2 << "targetNodeID" << " " << "exposure_level" << endl;
        vector<double> nodeExpLevels(n,0.0);

        for (int rcID = 0; rcID < rcSampleSize; rcID++) {
            int target = targetNodes[rcID];
            if(isCovered[rcID]) {
                for (std::set<double>::iterator it = rcSeen[rcID].begin() ; it != std::prev(rcSeen[rcID].end()); ++it){
                  double a=*it;
                  double b=*(std::next(it));
                  nodeExpLevels[target] += (a-b)*(a-b);
              }
            }
        }

        //            double kontrolAw = 0;
        for (int i = 0 ; i < n ; i++) {
            double tempVal = nodeExpLevels[i];
            nodeExpLevels[i] = (double) n * tempVal / (double) rcSampleSize;
            //                kontrolAw += nodeExpLevels[i];
            extraStream2 << i << " " << nodeExpLevels[i] << endl;
        }

        extraStream2.close();
        //            cout << "kontrol " << kontrolAw << endl;

        //        } // end of extra results



        return totalExpScore / (double) rcSampleSize;
    }

    double allocator::degreeWeighted(int64 rcSampleSize, int k) {


              clock_t begin = clock();

              priority_queue<pair<int, double>, vector<pair<int, double>>, CompareBySecond>heap;
              std::vector<double> divExpScore(nrPairs, 0);
              std::vector<int> attentionQuota = std::vector<int>(n,kappa);

      //        std::vector<double> rcMinSeen(rcSampleSize,-5.0);
      //        std::vector<double> rcMaxSeen(rcSampleSize, 5.0);

              std::vector<set<double>> rcSeen(rcSampleSize);
              std::vector<set<double>> nodeSeen(n);

              for (int i=0; i< n; i++){
                nodeSeen[i].insert(-1.0);
                nodeSeen[i].insert(1.0);
                nodeSeen[i].insert(nodeLeanings[i]);
              }


              vector<bool> isCovered(rcSampleSize, false);
              vector<bool> pairMark(nrPairs, true);

              double totalExpScore = 0;
              int bestPairID, bestNodeID, bestItemID;


              divExpScore = hyper_degree;

              for (int i = 0; i < n; i++) {
                  double val = (double) nodeDegree[i];
                  std::pair<int, double>pairVal(std::make_pair(i, val));
                  heap.push(pairVal);
              }

              seedSet.clear();
              seedScores.clear();


              while ((int)seedSet.size() < k) {

                  pair<int, double> pairVal = heap.top();
                  bestNodeID = pairVal.first;
                  attentionQuota[bestNodeID]--;

                  if(attentionQuota[bestNodeID] == 0) { //if the attention quota for this node is topped already, pop it from the queue forevah
                      heap.pop();
                  }



                  double itMax = 0;
                  bestItemID=-1;
                  for (int itemID = 0; itemID < nrItems; itemID++) {
                      int pairIDtemp = bestNodeID + n * itemID;
                      if (pairMark[pairIDtemp]) { // if this item is not assigned to this node yet
                          std::set<double> tempNodeSeen;
                          tempNodeSeen=nodeSeen[bestNodeID];
                          tempNodeSeen.insert(itemLeanings[itemID]);
                          double c,d, diff;
                          if (itemLeanings[itemID]==-1.0){
                            c=-1.0;
                          }
                          else{
                            c=double(*(std::prev(tempNodeSeen.find(itemLeanings[itemID]))));
                          }
                          if (itemLeanings[itemID]==1.0){
                            d=1.0;
                          }
                          else{
                            d=double(*(std::next(tempNodeSeen.find(itemLeanings[itemID]))));
                          }
                          diff=(c-itemLeanings[itemID])*(c-itemLeanings[itemID])+(itemLeanings[itemID]-d)*(itemLeanings[itemID]-d) - (c-d)*(c-d);
                          if(itMax >= diff ) {
                              itMax = diff;
                              bestItemID = itemID;
                          }
                      }
                  }
                  if (bestItemID==-1){
                    cout << "error. best item not found.";
                    exit(1);
                  }
                  nodeSeen[bestNodeID].insert(itemLeanings[bestItemID]);
                  bestPairID = bestNodeID + n * bestItemID;
                  totalExpScore += divExpScore[bestPairID];
                  seedSet.push_back(bestPairID);
                  seedScores.push_back(n * divExpScore[bestPairID] / (double) rcSampleSize);
                  pairMark[bestPairID] = false;

                  // update the hyper_degree of the pairs whose marginal gain change due to the best pair selection
                  vector<int> rcsAffected = hyperG[bestPairID]; // ids of RC sets that contain this best pair
                  for (int j = 0; j < rcsAffected.size(); j++) {
                      int rcID = rcsAffected[j];
                      int target = targetNodes[rcID];

                      // if it is the first time this RC is covered by a seed pair -- below the marginal gain update operations for this case
                      if (!isCovered[rcID]) {
                          isCovered[rcID] = true;
      //                    rcMinSeen[rcID] = std::min(nodeLeanings[target], itemLeanings[bestItemID]);
      //                    rcMaxSeen[rcID] = std::max(nodeLeanings[target], itemLeanings[bestItemID]);
                          rcSeen[rcID].insert(-1.0);
                          rcSeen[rcID].insert(nodeLeanings[target]);
                          rcSeen[rcID].insert(1.0);
                     }

                          //New diversity function implementation
                          rcSeen[rcID].insert(itemLeanings[bestItemID]);
                          double a,b;
                          a=double(*(std::prev(rcSeen[rcID].find(itemLeanings[bestItemID]))));
                          b=double(*(std::next(rcSeen[rcID].find(itemLeanings[bestItemID]))));

                            // compute the amount of change in marginal gain for each item contained in this RC set
                            for(int itemID = 0; itemID < nrItems; itemID++) {
                              if (itemLeanings[itemID] <= a  || itemLeanings[itemID] >= b ){
                                continue;
                              }
                              double prev_quad, new_quad;
                              if(itemLeanings[itemID] < itemLeanings[bestItemID]){
                                prev_quad=(itemLeanings[itemID]-b)*(itemLeanings[itemID]-b);
                                new_quad=(itemLeanings[itemID]-itemLeanings[bestItemID])*(itemLeanings[itemID]-itemLeanings[bestItemID])+(itemLeanings[bestItemID]-b)*(itemLeanings[bestItemID]-b);
                              }
                              else{
                                prev_quad=(a-itemLeanings[itemID])*(a-itemLeanings[itemID]);
                                new_quad=(a-itemLeanings[bestItemID])*(a-itemLeanings[bestItemID])+(itemLeanings[bestItemID]-itemLeanings[itemID])*(itemLeanings[bestItemID]-itemLeanings[itemID]);
                              }
                            vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                            for (int z = 0; z < rrTemp.size(); z++) {
                                int pairID = rrTemp[z] + n * itemID;
                                if(pairMark[pairID]) {
                                    double tempD = divExpScore[pairID];
                                    divExpScore[pairID] = tempD-new_quad+prev_quad;
                                    if(divExpScore[pairID] < 0) {
                                        divExpScore[pairID] = 0;
                                    }

                                }
                            }
                         }
      /*
                          // compute the amount of change in marginal gain for each item contain in this RC set
                          for(int itemID = 0; itemID < nrItems; itemID++) {

                              prevGain = std::abs(nodeLeanings[target] - itemLeanings[itemID]); // mg to empty set
                              if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                                  currGain = 0;
                              }
                              else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                                  currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                              }
                              else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                                  currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                              }
                              vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                              for (int z = 0; z < rrTemp.size(); z++) {
                                  int pairID = rrTemp[z] + n * itemID;
                                  if(pairMark[pairID]) {
                                      double tempD = divExpScore[pairID];
                                      divExpScore[pairID] = tempD - prevGain + currGain;
                                      if(divExpScore[pairID] < 0) {
                                          divExpScore[pairID] = 0;
                                      }
                                  }//
                              }
                          }
                      }

                      // if it was already covered before
                      else {
                          if(itemLeanings[bestItemID] >= rcMinSeen[rcID] && itemLeanings[bestItemID] <= rcMaxSeen[rcID])
                              continue;

                          double prevMin = rcMinSeen[rcID];
                          double prevMax = rcMaxSeen[rcID];
                          rcMinSeen[rcID] = std::min(prevMin, itemLeanings[bestItemID]);
                          rcMaxSeen[rcID] = std::max(prevMax, itemLeanings[bestItemID]);

                          for(int itemID = 0; itemID < nrItems; itemID++) {
                              if (itemLeanings[itemID] >= prevMin &&  itemLeanings[itemID] <= prevMax) {
                                  prevGain = 0;
                              }
                              else if(itemLeanings[itemID] < prevMin) {
                                  prevGain = prevMin - itemLeanings[itemID];
                              }
                              else if(itemLeanings[itemID] > prevMax) {
                                  prevGain = itemLeanings[itemID] - prevMax;
                              }

                              if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                                  currGain = 0;
                              }
                              else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                                  currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                              }
                              else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                                  currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                              }

                              vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                              for (int z = 0; z < rrTemp.size(); z++) {
                                  int pairID = rrTemp[z] + n * itemID;
                                  if(pairMark[pairID]) {
                                      double tempD = divExpScore[pairID];
                                      divExpScore[pairID] = tempD - prevGain + currGain;
                                      if(divExpScore[pairID] < 0) {
                                          divExpScore[pairID] = 0;
                                      }
                                  }
                              }
                          }
                      } // end-if this RC was already covered before
      */
                  }// end of for loop for affected
              } // end of while k loop

              clock_t end = clock();
              totalDuration = (double(end - begin) / CLOCKS_PER_SEC) + duration_common; // in seconds
              totalMemory = getCurrentMemoryUsage(); // in MB

              cout << "total degree-myopic time taken (in seconds) " << totalDuration << " total memory (in mb) " << totalMemory << endl;

              string extraFName0 = outFolderName + OS_SEP + "assignment_degreeFar.txt";
              ofstream extraStream0;
              if(extraStream0.is_open())
                  extraStream0.close();

              extraStream0.open(extraFName0.c_str());

              if (extraStream0.is_open() == false) {
                  cout << "Can't open file " << extraFName0  << " for writing" << endl;
                  exit(1);
              }

              extraStream0 << "nodeID" << " " << "itemID" << " " <<  "mgScore" << " " << "cumScore" << " " << "duration(sec)" << " " << "memory(mb)" << endl;
              double totMGs = 0;
              for (int i = 0; i < seedSet.size(); i++) {
                  int node = (int) seedSet[i] % n;
                  int item = (int) seedSet[i] / n;
                  totMGs += seedScores[i];
                  extraStream0 << node << " " << item << " " << seedScores[i] << " " << totMGs << " " << totalDuration << " " << totalMemory << endl;
              }
              cout << "total degree-myopic div. exp. score " << totMGs << endl;
              extraStream0.close();


              // compute for each seed pair its prob. of reaching target nodes

              string extraFName1 = outFolderName + OS_SEP + "pairReachProbs_degreeFar.txt";
              ofstream extraStream1;

              if(extraStream1.is_open())
                  extraStream1.close();

              extraStream1.open(extraFName1.c_str());

              if (extraStream1.is_open() == false) {
                  cout << "Can't open file " << extraFName1  << " for writing" << endl;
                  exit(1);
              }

              extraStream1 << "nodeID" << " " << "itemID" << " " <<  "targetNodeID" << " " << "reachProb" << endl;

              extraStream1 << std::fixed;
              extraStream1.precision(8);

              vector< vector<double> > pairNodeReachProbs;

              for (int i = 0; i < k; i++) {
                  pairNodeReachProbs.push_back(std::vector<double>(n,0.0));
              }

              for (int i = 0; i < k; i++) {
                  int seedPairID = seedSet[i];
                  vector<int> rcsCovered = hyperG[seedPairID]; // ids of RC sets that contain this best pair
                  for (int j = 0; j < rcsCovered.size(); j++) {
                      int rcID = rcsCovered[j];
                      int target = targetNodes[rcID];
                      double tempVal = pairNodeReachProbs[i][target];
                      pairNodeReachProbs[i][target] = tempVal + 1.0;
                  }
              }

              for (int i = 0; i < k; i++) {
                  int seedPairID = seedSet[i];
                  int nodeID = (int) seedPairID % n;
                  int itemID = (int) seedPairID / n;
                  for (int j = 0; j < n; j++) {
                      double tempVal = pairNodeReachProbs[i][j];
                      pairNodeReachProbs[i][j] = (double) n * tempVal / (double) rcSampleSize;
                      extraStream1 << nodeID << " " << itemID << " " <<  j << " " << pairNodeReachProbs[i][j] << endl;
                  }
              }

              extraStream1.close();

              // compute fv(seedset) for each target node v
              string extraFName2 = outFolderName + OS_SEP + "nodeExpLevels_degreeFar.txt";
              ofstream extraStream2;

              if(extraStream2.is_open())
                  extraStream2.close();

              extraStream2.open(extraFName2.c_str());

              if (extraStream2.is_open() == false) {
                  cout << "Can't open file " << extraFName2  << " for writing" << endl;
                  exit(1);
              }

              extraStream2 << "targetNodeID" << " " << "exposure_level" << endl;
              vector<double> nodeExpLevels(n,0.0);

              for (int rcID = 0; rcID < rcSampleSize; rcID++) {
                  int target = targetNodes[rcID];
                  if(isCovered[rcID]) {
                    for (std::set<double>::iterator it = rcSeen[rcID].begin() ; it != std::prev(rcSeen[rcID].end()); ++it){
                     double a=*it;
                     double b=*(std::next(it));
                      nodeExpLevels[target] += (a-b)*(a-b);
                    }
                  }
              }

              //            double kontrolAw = 0;
              for (int i = 0 ; i < n ; i++) {
                  double tempVal = nodeExpLevels[i];
                  nodeExpLevels[i] = (double) n * tempVal / (double) rcSampleSize;
                  //                kontrolAw += nodeExpLevels[i];
                  extraStream2 << i << " " << nodeExpLevels[i] << endl;
              }

              extraStream2.close();
              //            cout << "kontrol " << kontrolAw << endl;

              //        } // end of extra results



              return totalExpScore / (double) rcSampleSize;
/*
        clock_t begin = clock();
        priority_queue<pair<int, double>, vector<pair<int, double>>, CompareBySecond>heap;
        std::vector<double> divExpScore(nrPairs, 0);
        std::vector<int> attentionQuota = std::vector<int>(n,kappa);

        std::vector<double> rcMinSeen(rcSampleSize,-5.0);
        std::vector<double> rcMaxSeen(rcSampleSize, 5.0);

        vector<bool> isCovered(rcSampleSize, false);
        vector<bool> pairMark(nrPairs, true);

        double totalExpScore = 0;
        int bestPairID, bestNodeID, bestItemID;

        for (int i = 0; i < n; i++) {
            for (int itemID = 0; itemID < nrItems; itemID++) {
                int prID = i + n * itemID;
                double val = ((double) nodeDegree[i]) * (std::abs(nodeLeanings[i] - itemLeanings[itemID]));
                std::pair<int, double>pairVal(std::make_pair(prID, val));
                heap.push(pairVal);
                divExpScore[prID] = hyper_degree[prID];
            }
        }


        seedSet.clear();
        seedScores.clear();


        while ((int)seedSet.size() < k) {

            pair<int, double> pairVal = heap.top();
            heap.pop();
            bestPairID = pairVal.first;
            bestNodeID = (int) bestPairID % n;
            // if the attention quota for this node is filled, remove it from queue and contimue
            if(attentionQuota[bestNodeID] == 0)
                continue;


            bestItemID = (int) bestPairID / n;
            totalExpScore += divExpScore[bestPairID];
            seedSet.push_back(bestPairID);
            seedScores.push_back(n * divExpScore[bestPairID] / (double) rcSampleSize);
            pairMark[bestPairID] = false;
            attentionQuota[bestNodeID]--;

            // update the hyper_degree of the pairs whose marginal gain change due to the best pair selection
            vector<int> rcsAffected = hyperG[bestPairID]; // ids of RC sets that contain this best pair
            for (int j = 0; j < rcsAffected.size(); j++) {
                int rcID = rcsAffected[j];
                int target = targetNodes[rcID];
                double prevGain, currGain;

                // if it is the first time this RC is covered by a seed pair -- below the marginal gain update operations for this case
                if (!isCovered[rcID]) {
                    isCovered[rcID] = true;
                    rcMinSeen[rcID] = std::min(nodeLeanings[target], itemLeanings[bestItemID]);
                    rcMaxSeen[rcID] = std::max(nodeLeanings[target], itemLeanings[bestItemID]);

                    // compute the amount of change in marginal gain for each item contain in this RC set
                    for(int itemID = 0; itemID < nrItems; itemID++) {

                        prevGain = std::abs(nodeLeanings[target] - itemLeanings[itemID]); // mg to empty set
                        if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                            currGain = 0;
                        }
                        else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                            currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                            currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                        }
                        vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                        for (int z = 0; z < rrTemp.size(); z++) {
                            int pairID = rrTemp[z] + n * itemID;
                            if(pairMark[pairID]) {
                                double tempD = divExpScore[pairID];
                                divExpScore[pairID] = tempD - prevGain + currGain;
                                if(divExpScore[pairID] < 0) {
                                    divExpScore[pairID] = 0;
                                }
                            }//
                        }
                    }
                }

                // if it was already covered before
                else {
                    if(itemLeanings[bestItemID] >= rcMinSeen[rcID] && itemLeanings[bestItemID] <= rcMaxSeen[rcID])
                        continue;

                    double prevMin = rcMinSeen[rcID];
                    double prevMax = rcMaxSeen[rcID];
                    rcMinSeen[rcID] = std::min(prevMin, itemLeanings[bestItemID]);
                    rcMaxSeen[rcID] = std::max(prevMax, itemLeanings[bestItemID]);

                    for(int itemID = 0; itemID < nrItems; itemID++) {
                        if (itemLeanings[itemID] >= prevMin &&  itemLeanings[itemID] <= prevMax) {
                            prevGain = 0;
                        }
                        else if(itemLeanings[itemID] < prevMin) {
                            prevGain = prevMin - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > prevMax) {
                            prevGain = itemLeanings[itemID] - prevMax;
                        }

                        if (itemLeanings[itemID] >= rcMinSeen[rcID] &&  itemLeanings[itemID] <= rcMaxSeen[rcID]) {
                            currGain = 0;
                        }
                        else if(itemLeanings[itemID] < rcMinSeen[rcID]) {
                            currGain = rcMinSeen[rcID] - itemLeanings[itemID];
                        }
                        else if(itemLeanings[itemID] > rcMaxSeen[rcID]) {
                            currGain = itemLeanings[itemID] - rcMaxSeen[rcID];
                        }

                        vector<int> rrTemp = rcList->at(itemID)->hyperGT[rcID];
                        for (int z = 0; z < rrTemp.size(); z++) {
                            int pairID = rrTemp[z] + n * itemID;
                            if(pairMark[pairID]) {
                                double tempD = divExpScore[pairID];
                                divExpScore[pairID] = tempD - prevGain + currGain;
                                if(divExpScore[pairID] < 0) {
                                    divExpScore[pairID] = 0;
                                }
                            }
                        }
                    }
                } // end-if this RC was already covered before

            }// end of for loop for affected
        } // end of while k loop


        clock_t end = clock();
        totalDuration = (double(end - begin) / CLOCKS_PER_SEC) + duration_common; // in seconds
        totalMemory = getCurrentMemoryUsage(); // in MB

        cout << "total degree-weighted time taken (in seconds) " << totalDuration << " total memory (in mb) " << totalMemory << endl;

        string extraFName0 = outFolderName + OS_SEP + "assignment_degreeWeighted.txt";
        ofstream extraStream0;
        if(extraStream0.is_open())
            extraStream0.close();

        extraStream0.open(extraFName0.c_str());

        if (extraStream0.is_open() == false) {
            cout << "Can't open file " << extraFName0  << " for writing" << endl;
            exit(1);
        }

        extraStream0 << "nodeID" << " " << "itemID" << " " <<  "mgScore" << " " << "cumScore" << " " << "duration(sec)" << " " << "memory(mb)" << endl;
        double totMGs = 0;
        for (int i = 0; i < seedSet.size(); i++) {
            int node = (int) seedSet[i] % n;
            int item = (int) seedSet[i] / n;
            totMGs += seedScores[i];
            extraStream0 << node << " " << item << " " << seedScores[i] << " " << totMGs << " " << totalDuration << " " << totalMemory << endl;
        }
        cout << "total degree-weighted div. exp. score " << totMGs << endl;

        extraStream0.close();



        // compute for each seed pair its prob. of reaching target nodes

        string extraFName1 = outFolderName + OS_SEP + "pairReachProbs_degreeWeighted.txt";
        ofstream extraStream1;

        if(extraStream1.is_open())
            extraStream1.close();

        extraStream1.open(extraFName1.c_str());

        if (extraStream1.is_open() == false) {
            cout << "Can't open file " << extraFName1  << " for writing" << endl;
            exit(1);
        }

        extraStream1 << "nodeID" << " " << "itemID" << " " <<  "targetNodeID" << " " << "reachProb" << endl;

        extraStream1 << std::fixed;
        extraStream1.precision(8);

        vector< vector<double> > pairNodeReachProbs;

        for (int i = 0; i < k; i++) {
            pairNodeReachProbs.push_back(std::vector<double>(n,0.0));
        }

        for (int i = 0; i < k; i++) {
            int seedPairID = seedSet[i];
            vector<int> rcsCovered = hyperG[seedPairID]; // ids of RC sets that contain this best pair
            for (int j = 0; j < rcsCovered.size(); j++) {
                int rcID = rcsCovered[j];
                int target = targetNodes[rcID];
                double tempVal = pairNodeReachProbs[i][target];
                pairNodeReachProbs[i][target] = tempVal + 1.0;
            }
        }

        for (int i = 0; i < k; i++) {
            int seedPairID = seedSet[i];
            int nodeID = (int) seedPairID % n;
            int itemID = (int) seedPairID / n;
            for (int j = 0; j < n; j++) {
                double tempVal = pairNodeReachProbs[i][j];
                pairNodeReachProbs[i][j] = (double) n * tempVal / (double) rcSampleSize;
                extraStream1 << nodeID << " " << itemID << " " <<  j << " " << pairNodeReachProbs[i][j] << endl;
            }
        }

        extraStream1.close();

        // compute fv(seedset) for each target node v
        string extraFName2 = outFolderName + OS_SEP + "nodeExpLevels_degreeWeighted.txt";
        ofstream extraStream2;

        if(extraStream2.is_open())
            extraStream2.close();

        extraStream2.open(extraFName2.c_str());

        if (extraStream2.is_open() == false) {
            cout << "Can't open file " << extraFName2  << " for writing" << endl;
            exit(1);
        }

        extraStream2 << "targetNodeID" << " " << "exposure_level" << endl;
        vector<double> nodeExpLevels(n,0.0);

        for (int rcID = 0; rcID < rcSampleSize; rcID++) {
            int target = targetNodes[rcID];
            if(isCovered[rcID]) {
                nodeExpLevels[target] += (rcMaxSeen[rcID] - rcMinSeen[rcID]);
            }
        }

        //            double kontrolAw = 0;
        for (int i = 0 ; i < n ; i++) {
            double tempVal = nodeExpLevels[i];
            nodeExpLevels[i] = (double) n * tempVal / (double) rcSampleSize;
            //                kontrolAw += nodeExpLevels[i];
            extraStream2 << i << " " << nodeExpLevels[i] << endl;
        }

        extraStream2.close();
        //            cout << "kontrol " << kontrolAw << endl;

        //        } // end of extra results



        return totalExpScore / (double) rcSampleSize;



*/
    }

  
    void allocator::readTICGraph() {

        string probGraphFile = opt->getValue("probGraphFile");
        cout << "Reading file " << probGraphFile << endl;
        ifstream myfile (probGraphFile.c_str(), ios::in);

        double *itemProbs; //item-specific influence probabilities

        int nrEdges = 0;
        set<int> nodes; // for control

        if (myfile.is_open()) {
            while (! myfile.eof() )         {
                std::string line;
                getline (myfile,line);
                if (line.empty()) continue;

                std::string::size_type pos = line.find_first_of(delim);
                int prevpos = 0;

                //first user
                string str = line.substr(prevpos, pos-prevpos);
                int u1 = strToInt(str);

                //second user
                prevpos = line.find_first_not_of(delim, pos);
                pos = line.find_first_of(delim, prevpos);
                int u2 = strToInt(line.substr(prevpos, pos-prevpos));

                if (u1 == u2)
                    continue;

                nodeDegree[u1] = nodeDegree[u1] + 1.0;

                nrEdges++;

                graphT[u2].push_back(u1); //insert to the transposed graph

                // for control
                nodes.insert(u1);
                nodes.insert(u2);

//                continue;

//                prevpos = line.find_first_not_of(delim, pos);
//
//                str = line.substr(prevpos);
//                itemProbs = new double[nrItems];
//                stringTokenizer(str, itemProbs, nrItems, delim);

//                // cide : only here
//                for(int i = 0; i < nrItems; i++) {
                    //double hede = std::min(itemProbs[i] + 0.01, 1.0);
//                    rcList->at(i)->probT[u2].push_back(itemProbs[i]);
//                    // multi-item test icin
////                    rcList->at(i)->probT[u2].push_back(itemProbs[0]);
//                }

            }

            // verify input
            if (n != (int) nodes.size()) {
                cout << "problem: nr of nodes read is not equal to input n, exiting..." << endl;
                exit(1);
            }

            if (m != (int) nrEdges) {
                                cout << "read this nr of edges " << nrEdges << endl;
                cout << "problem: nr of edges read is not equal to input m, exiting..." << endl;
                exit(1);
            }

//            cout << "node ids kontrol " << endl;
//            for (set<int>::iterator it = nodes.begin(); it != nodes.end(); it++) {
//                cout << (*it) << " ";
//            }
//            cout << endl;

            myfile.close();
        }

        else
            cout << "Can't open input graph file " << probGraphFile << endl;

        cout << "graph import complete " << endl;
        cout << "total number of nodes " << nodes.size() << endl;
        cout << "total number of edges " << nrEdges << endl;
    }

/*
// The following is the non-weighted cascade function
    void allocator::readTICGraph() {

        string probGraphFile = opt->getValue("probGraphFile");
        cout << "Reading file " << probGraphFile << endl;
        ifstream myfile (probGraphFile.c_str(), ios::in);

        double *itemProbs; //item-specific influence probabilities

        int nrEdges = 0;
        set<int> nodes; // for control

        if (myfile.is_open()) {
            while (! myfile.eof() )	{
                std::string line;
                getline (myfile,line);
                if (line.empty()) continue;

                std::string::size_type pos = line.find_first_of(delim);
                int prevpos = 0;

                //first user
                string str = line.substr(prevpos, pos-prevpos);
                int u1 = strToInt(str);

                //second user
                prevpos = line.find_first_not_of(delim, pos);
                pos = line.find_first_of(delim, prevpos);
                int u2 = strToInt(line.substr(prevpos, pos-prevpos));

                if (u1 == u2)
                    continue;

                nodeDegree[u1] = nodeDegree[u1] + 1.0;

                nrEdges++;

                graphT[u2].push_back(u1); //insert to the transposed graph

                // for control
                nodes.insert(u1);
                nodes.insert(u2);

                prevpos = line.find_first_not_of(delim, pos);

                str = line.substr(prevpos);
                itemProbs = new double[nrItems];
                stringTokenizer(str, itemProbs, nrItems, delim);


                for(int i = 0; i < nrItems; i++) {
                    rcList->at(i)->probT[u2].push_back(itemProbs[i]);
                }

            }

            // verify input
            if (n != (int) nodes.size()) {
                cout << "problem: nr of nodes read is not equal to input n, exiting..." << endl;
                exit(1);
            }

            if (m != (int) nrEdges) {
                cout << "problem: nr of edges read is not equal to input m, exiting..." << endl;
                exit(1);
            }

//            cout << "node ids kontrol " << endl;
//            for (set<int>::iterator it = nodes.begin(); it != nodes.end(); it++) {
//                cout << (*it) << " ";
//            }
//            cout << endl;

            myfile.close();
        }

        else
            cout << "Can't open input graph file " << probGraphFile << endl;

        cout << "graph import complete " << endl;
        cout << "total number of nodes " << nodes.size() << endl;
        cout << "total number of edges " << nrEdges << endl;
    }


*/


    void allocator::readItemLeaningsFile() {
        cout << "reading item leanings file " << endl;
        string itemLeaningsFile = opt->getValue("itemLeaningsFile");
        ifstream myfile(itemLeaningsFile.c_str(), ios::in);

        int itemIndex = 0;

        if(myfile.is_open()) {
            while(!myfile.eof()) {
                std::string line;
                getline(myfile, line);
                if(line.empty())
                    continue;
                itemLeanings.push_back(strToDouble(line));
                if(++itemIndex == nrItems)
                    break;
            }
            myfile.close();
        }
        else {
            cout << "problem opening the item leanings file, exiting... " <<  endl;
            exit(1);
        }
    }

    void allocator::readNodeLeaningsFile() {
        cout << "reading node leanings file " << endl;
        string nodeLeaningsFile = opt->getValue("nodeLeaningsFile");
        ifstream myfile(nodeLeaningsFile.c_str(), ios::in);

        int nodeIndex = 0;

        if(myfile.is_open()) {
            while(!myfile.eof()) {
                std::string line;
                getline(myfile,line);
//                cout << "line " << line << endl;
                if(line.empty())
                    continue;
//                nodeLeaningsFile[nodeIndex] = strToDouble(line);
                nodeLeanings.push_back(strToDouble(line));
                if(++nodeIndex == n)
                    break;
            }
            myfile.close();
//            cout << "size " << nodeLeanings.size() << endl;
        }
        else {
            cout << "problem opening the node leanings file, exiting... " << nodeLeaningsFile << endl;
            exit(1);
        }
    }

    allocator::~allocator() {
        cout << "assignments complete! " << endl;
    }

    void allocator::arrangeOutputFiles() {

                string command = string("mkdir -p ") + outFolderName ;

                system(command.c_str());


        string masterFileName = "assignment_tdem.txt";
        outMasterName = outFolderName + OS_SEP + masterFileName;
//        outMasterName = masterFileName;

        if(outMasterStream.is_open())
            outMasterStream.close();

        outMasterStream.open(outMasterName.c_str());

        outMasterStream << "nodeID" << " " << "itemID" << " " <<  "mgScore" << " " << "cumScore" << " " << "duration(sec)" << " " << "memory(mb)" << endl;

        if (outMasterStream.is_open() == false) {
            cout << "Can't open file " << outMasterName  << " for writing" << endl;
            exit(1);
        }

        // memory icin
        command = string("mkdir -p temp") ;
        system(command.c_str());
    }

    //    void allocator::writeInMasterOutputFile(int nodeID, int itemID) {
    //        // seed-node item mgScore totScore runTime(sec) memory(mb)
    //        outMasterStream << nodeID << " " << itemID << endl;
    //    }


    void allocator::writeInMasterOutputFile(int nodeID, int itemID, double mgScore, double totScore, float duration, float memory) {
        // seed-node item mgScore totScore runTime(sec) memory(mb)
        outMasterStream << nodeID << " " << itemID << " " <<  mgScore << " " << totScore << " " << duration << " " << memory << endl;
    }


}
