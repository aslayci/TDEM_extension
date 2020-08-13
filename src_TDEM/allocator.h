#ifndef ALLOCATOR_H
#define ALLOCATOR_H

#include <iostream>
#include <algorithm>
#include <vector>
#include <set>
#include <ctime>
#include <cmath>
#include <sys/types.h>
#include <sys/stat.h>
#include <queue>
#include <utility>
#include "sfmt/SFMT.h"

#include "itemGraph.h"
#include "anyoption.h"
#include "utils.h"


//typedef std::pair<double,int> infPair;

namespace _Cide{
    
    struct CompareBySecond {
        bool operator()(std::pair<int,double> a, std::pair<int,double> b) {
            return a.second < b.second;
        }
    };
    
    //typedef std::vector<vector<int>> RRSample; // hyperGT (i.e., RR sets sample) of an item
    typedef std::vector<itemGraph*> itemGraphList; // to reference RC sets sample from coordinated RR samples of items - size = nrItems
    
    class allocator {
        
    public:
        
        allocator(AnyOption* opt);
        ~allocator();
        
        time_t startTime;
        double duration_common;
        int64 theta; 
    
        // problem parameters
        AnyOption *opt;
        int n, m, nrItems, nrPairs, kappa, k;
        double epsilon, delta, ell;
    
        std::vector<double> nodeLeanings;
        std::vector<double> itemLeanings;
        std::vector<int> seedSet;
        std::vector<double> seedScores;
        std::vector<double> nodeDegree;
        
        // RC-sampling related
        sfmt_t sfmtSeed;
        itemGraphList *rcList; // contains references to coordinated RR sets of item graphs
        std::vector< std::vector<int> > hyperG;
        std::vector<double> hyper_degree;
        vector<int> targetNodes;
        int64 prevSize;
        
        double tdem();
        double lowerBoundOPT();
        void generateRCSets(int64 newSize);
        double rcGreedy(int64 rcSampleSize, int k, bool extraResults);
        double degreeClose(int64 rcSampleSize, int k);
        double degreeFar(int64 rcSampleSize, int k);
        double degreeWeighted(int64 rcSampleSize, int k);
        
        
        // time and memory
        float totalDuration; // in seconds
        float totalMemory; // in MB
        
        // IO operations
        string delim;
        void readTICGraph();
        void readItemLeaningsFile();
        void readNodeLeaningsFile();
        
        void writeInMasterOutputFile(int nodeID, int itemID, double mgScore, double totScore, float duration, float memory);
//        void writeInMasterOutputFile(int nodeID, int itemID);
        void arrangeOutputFiles();
        
        ofstream outMasterStream;
        string outFolderName;
        string outMasterName;
        
    };


}


#endif
