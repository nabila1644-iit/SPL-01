#include<iostream>
#include<string>
#include<sstream>
#include<fstream>
#include<vector>
#include<set>
#include<map>
#include<cmath>

using namespace std;
using namespace std::chrono;

int transactions = 0;
double minimum_support=0.4;
double min_confidence=0.5;

template<typename Iterator>
void my_sort(Iterator first,Iterator last){
    auto count=last-first;
    if(count<2){
        return;
    }
    auto pivot=*(first+count/2);
    Iterator left=first;
    Iterator right=last-1;
    while(left<=right){
        while (*left<pivot)
        {
            ++left;
        }
        while(*right>pivot){
            --right;
        }
        if(left<=right){
            iter_swap(left,right);
            ++left;
            --right;
        }
        
    }
    if(first<right+1){
        my_sort(first,right+1);
    }
    if(left<last){
        my_sort(left,last);
    }
}

void printItemset(const vector<int>&itemset){
    cout<<"{";
    int n=itemset.size();
    for(int i=0;i<n;i++){
        cout<<"I"<<(itemset[i]+1);
        if(i<n-1){
            cout<<",";
        }
    }
    cout<<"}";
}

void convertFile(const string &inputFile, const string &outputFile) {
    ifstream in(inputFile);
    ofstream out(outputFile);
    string line;
    //database.clear();
    
    while(getline(in, line)) {
        for(char &ch : line) {
            if(ch == ',' || ch == ':') {
                ch = ' ';
            }
        }
        transactions++;
        out << line << endl;
        
    }
    in.close();
    out.close();
    cout<<"total transactions "<<transactions<<endl;
}
//APRIORI HELPER FUNCTIONS 
void parseTransaction(const string &line,vector<int>&transaction_items){
    transaction_items.clear();
    set<int>items;
    stringstream ss(line);
    string word;
    while(ss>>word){
        if(word[0]=='I' && word.length()>1){
            int item_index=stoi(word.substr(1))-1;
            if(item_index>=0){
                items.insert(item_index);
            }
        }
    }
    transaction_items.assign(items.begin(),items.end());
}

bool isSortedSubset(const vector<int>&transaction_items,const vector<int>&itemSet){
    int i=0;
    int j=0;
    int trans_size=transaction_items.size();
    int itemSet_size=itemSet.size();
    if(itemSet_size>trans_size){
        return false;

    }
    while(i<trans_size && j<itemSet_size){
        if(transaction_items[i]<itemSet[j]){
            i++;
        }
        else if(transaction_items[i]==itemSet[j]){
            i++;
            j++;
        }
        else{
            return false;
        }
    }
    return (j==itemSet_size);
}

bool canJoin(const vector<int>&itemset1,const vector<int>&itemset2,int k){
    for(int i=0;i<k-2;i++){
        if(itemset1[i]!=itemset2[i]){
            return false;
        }
    }
    return itemset1[k-2]<itemset2[k-2];
}


vector<vector<int>>generateCandidates(const vector<vector<int>>&frequent_items,int k){
    vector<vector<int>>candidates;
    set<vector<int>>frequent_item_set(frequent_items.begin(),frequent_items.end());
    int n=frequent_items.size();
    for(int i=0;i<n;i++){
        for(int j=i+1;j<n;j++){
            if(canJoin(frequent_items[i],frequent_items[j],k)){
                vector<int>new_candidate=frequent_items[i];
                new_candidate.push_back(frequent_items[j][k-2]);
                bool has_infrequent_subset=false;
                int new_candidate_size=new_candidate.size();
                for(int m=0;m<new_candidate_size;m++){
                    vector<int>subset=new_candidate;
                    subset.erase(subset.begin()+m);
                    if(frequent_item_set.find(subset)==frequent_item_set.end()){
                        has_infrequent_subset=true;
                        break;
                    }
                }
                if(!has_infrequent_subset){
                    candidates.push_back(new_candidate);
                }
            }
        }
    }
    return candidates;
}

vector<vector<int>>findFrequent_1_Itemsets(const string& filename,int minimum_support_count,map<vector<int>,int>&all_itemset_supports){
    map<int,int>item_counts;
    ifstream in(filename);
    string line;
    while(getline(in,line)){
        vector<int>transaction_items;
        parseTransaction(line,transaction_items);
        for(int item:transaction_items){
            item_counts[item]++;
        }
    }
    in.close();
    vector<vector<int>>frequent_1_itemsets;
    for (auto const& pair : item_counts) {
        int item = pair.first;   
        int count = pair.second; 

        if (count >= minimum_support_count) {
            vector<int> itemset = { item };
            frequent_1_itemsets.push_back(itemset);
            all_itemset_supports[itemset] = count;
        }
    }
    return frequent_1_itemsets;
}

map<vector<int>,int> countCandidateFrequencies(const string& filename,const vector<vector<int>>&candidates){
    map<vector<int>,int>candidate_count;
    for(const auto& cand:candidates){
        candidate_count[cand]=0;
    }
    ifstream in(filename);
    string line;
    while(getline(in,line)){
        vector<int>transaction_items;
        parseTransaction(line,transaction_items);
        for(const auto& candidate:candidates){
            if(isSortedSubset(transaction_items,candidate)){
                candidate_count[candidate] ++;
    
            }
        }
    }
    in.close();
    return candidate_count;
}

vector<vector<int>> getFrequentItems(const vector<vector<int>>&candidates,const map<vector<int>,int>&candidate_counts,int minimum_support_count,map<vector<int>,int>&all_itemset_supports){
    vector<vector<int>>frequent_itemsets;
    for(const auto& candidate:candidates){
        int count=candidate_counts.at(candidate);
        if(count>=minimum_support_count){
            frequent_itemsets.push_back(candidate);
            all_itemset_supports[candidate]=count;
        }
    }
    return frequent_itemsets;
}

void generateRulesRecursive(const vector<int>&itemset,vector<int>&antecedent,int index,const map<vector<int>,int>&all_itemset_supports){
    if(index==itemset.size()){
        if(antecedent.empty()|| antecedent.size()==itemset.size()){
            return;
        }
        vector<int>consequent;
        int i_itemset=0;
        int i_antecedent=0;
        while(i_itemset<itemset.size()){
            if(i_antecedent==antecedent.size() || itemset[i_itemset]<antecedent[i_antecedent]){
                consequent.push_back(itemset[i_itemset]);
                i_itemset++;
            }
            else if(itemset[i_itemset]==antecedent[i_antecedent]){
                i_itemset++;
                i_antecedent++;
            }
            else{
                i_antecedent++;
            }
        }
        double support_AB=all_itemset_supports.at(itemset);
        double support_A=all_itemset_supports.at(antecedent);
        double support_B=all_itemset_supports.at(consequent);
        double confidence=support_AB/support_A;
        if(confidence>=min_confidence){
            double lift=confidence/(support_B/transactions);
            printItemset(antecedent);
            cout<<"-> ";
            printItemset(consequent);
            cout<<"\nsupport: "<<(support_AB/transactions)*100<<endl;
            cout<<"confidence: "<<confidence*100<<"%"<<endl;
            cout<<"lift: "<<lift<<endl;
            if(lift > 1.1) {
                cout << ">> STRATEGY: Bundle these! They are often bought together.\n";
            }    
            else if(lift < 0.9) {
                cout << ">> STRATEGY: These are substitutes. Don't bundle them.\n";
            }    
        }
        return;
    }
    generateRulesRecursive(itemset,antecedent,index+1,all_itemset_supports);
    antecedent.push_back(itemset[index]);
    generateRulesRecursive(itemset,antecedent,index+1,all_itemset_supports);
    antecedent.pop_back();
}

void generateAndPrintRules(const map<int,vector<vector<int>>>&all_frequent_itemsets,const map<vector<int>,int>&all_itemset_supports){
    cout<<"\n---apriori rules (min confidence: "<<min_confidence*100<<"%)---"<<endl;
    for(auto const& entry:all_frequent_itemsets){
        int k=entry.first;
        const auto& itemsets=entry.second;
        if(k<2){
            continue;
        }
        for(const auto& itemset:itemsets){
            vector<int>antecedent;
            generateRulesRecursive(itemset,antecedent,0,all_itemset_supports);
        }
    }
}

void BuisnessAnalytics(map<vector<int>,int>&all_itemset_supports,int total_transactions){
    int choice;
    
    do{
        cout<<"\n===============\n";
        cout<<"SHOPKEEPERS MENU     \n";
        cout<<"1.PREDICT: probability of buying item x if user has {a,b..d}\n";
        cout<<"2.STRATEGY: which items should be placed together? \n";
        cout<<"0. exit to main menu \n";
        cout<<"enter choice: \n";
        cin>>choice;

        if(choice==1){
            int n_antecedent,n_consequent,item;
            vector<int>antecedent,full_set;
            cout<<"\n---prediction tool ----\n";
            cout<<"how many items are currently in your cart? \n";
            cin>>n_antecedent;
            cout<<"Enter the item id's (E.g: 1,3,5): \n";
            for(int i=0;i<n_antecedent;i++){
                cin>>item;
                antecedent.push_back(item-1);
            }

            cout<<"which item are you looking probability for? \n";
            cin>>item;
            int target_item=item-1;

            full_set=antecedent;
            full_set.push_back(target_item);

            my_sort(antecedent.begin(),antecedent.end());
            my_sort(full_set.begin(),full_set.end());

            if(all_itemset_supports.count(antecedent) &&  all_itemset_supports.count(full_set)){
                double support_A=all_itemset_supports[antecedent];
                double support_AB=all_itemset_supports[full_set];

                double confidence=(support_AB/support_A)*100.00;
                cout<<"\n>>> RESULT: "<<confidence<<"% probability.\n";
                
                if(confidence>50.00){
                    cout<<"YES...i recommend this item\n";
                }
                else{
                    cout<<"unlikely to buy...";
                }
            }
            else{
                cout<<"\n not enough data history to predict this combination \n";
            }
        }

        else if(choice==2){
            cout<<"\n----Shelf Placement Strategy (top associations)---\n";
            cout<<"Items that are bought together frequently (high co-occurrence):\n";

            bool found=false;
            for(auto const& [itemset,count]:all_itemset_supports){
                if(itemset.size()>=2){
                    double support_pct=(double)count/total_transactions;

                    if(support_pct>0.3){
                        found=true;
                        printItemset(itemset);
                        cout<<" bought together in "<<(support_pct*100)<<"% of visits\n";

                    }
                }
            }
            if(!found){
                cout<<"NO strong groups found.\n";
            }
            cout<<"\nTIP: place these items on the same asile or adjacent shelves.\n";
        }
    }
    while (choice!=0);
    
}

struct FPNode {
    int itemId;
    int count;
    FPNode* parent;
    map<int, FPNode*> children;
    FPNode* nodeLink;

    FPNode(int id, FPNode* p = nullptr) {
        itemId = id;
        count = 1;
        parent = p;
        nodeLink=nullptr;
    }
};

struct HeaderInfo{
    int count;
    FPNode* firstNode;
    FPNode* lastNode;
    HeaderInfo(){
        count=0;
        firstNode=nullptr;
        lastNode=nullptr;
    }
};

int parseItem(string word){
    if(word[0]=='I' && word.length()>1){
        try{
            return stoi(word.substr(1))-1;
        }
        catch(...){
            return -1;
        }
    }
    return -1;
}


string getItemName(int id) {
    stringstream ss;
    ss << "I" << (id + 1);
    return ss.str();
}

void manualSort(vector<int>& items, map<int, int>& globalFreq) {
    int n = items.size();
    if (n < 2) return;

    for (int i = 0; i < n - 1; i++) {
        for (int j = 0; j < n - i - 1; j++) {
            int itemA = items[j];
            int itemB = items[j + 1];
            
            int countA = globalFreq[itemA];
            int countB = globalFreq[itemB];

            bool swapNeeded = false;

            if (countB > countA) {
                swapNeeded = true; 
            }
            else if (countB == countA) {
                if (itemB < itemA) {
                    swapNeeded = true; 
                }
            }

            if (swapNeeded) {
                int temp = items[j];
                items[j] = items[j + 1];
                items[j + 1] = temp;
            }
        }
    }
}

void ManualSortresults(vector<pair<vector<int>,int>>&results){
    int n=results.size();
    for(int i=0;i<n-1;i++){
        for(int j=0;j<n-i-1;j++){
            if(results[j+1].first.size()<results[j].first.size()){
                auto temp=results[j];
                results[j]=results[j+1];
                results[j+1]=temp;
            }
        }
    }
}

void manualSortPairs(vector<pair<int,int>>&items){
    int n=items.size();
    if(n<2){
        return;
    }
    for(int i=0;i<n-1;i++){
        for(int j=0;j<n-i-1;j++){
            if(items[j].second>items[j+1].second){
                pair<int,int>temp=items[j];
                items[j]=items[j+1];
                items[j+1]=temp;
            }
        }
    }
}


void printTree(FPNode* node, string indent, bool isLast) {
    cout << indent;
    if (isLast) {
        cout << "\\-"; //denotes last child
        indent += "  ";
    } else {
        cout << "|-"; //denotes middle child
        indent += "| ";
    }
    if(node->itemId!=-1){
        cout << getItemName(node->itemId) << " (" << node->count << ")" << endl;
    }
    else{
        cout<<"ROOT"<<endl;
    }
    int childIndex = 0;
    int totalChildren = node->children.size();
    
    
    for (map<int, FPNode*>::iterator it = node->children.begin(); it != node->children.end(); ++it) {
        childIndex++;
        printTree(it->second, indent, (childIndex == totalChildren));
    }
}

void insertTree(const vector<int>&transaction,FPNode* root,map<int,HeaderInfo>&headerTable,int count=1){
    FPNode* curr=root;
    for(int itemId: transaction){
        if(curr->children.find(itemId)==curr->children.end()){
            FPNode* newNode=new FPNode(itemId,curr);
            newNode->count=count;
            curr->children[itemId]=newNode;

            if(headerTable[itemId].firstNode==nullptr){
                headerTable[itemId].firstNode=newNode;
                headerTable[itemId].lastNode=newNode;
            }
            else{
                headerTable[itemId].lastNode->nodeLink=newNode;
                headerTable[itemId].lastNode=newNode;
            }
        }
        else{
            curr->children[itemId]->count+=count;
        }
        curr=curr->children[itemId];
    }
}

void mineFP(map<int,HeaderInfo>&headerTable,int min_sup,vector<int>&prefix,vector<pair<vector<int>,int>>&results){
    vector<pair<int,int>>sortedItems;
    for(auto const& pair:headerTable){
        sortedItems.push_back({pair.first,pair.second.count});
    }

    manualSortPairs(sortedItems);

    for(auto const& itempair :sortedItems){
        int itemId=itempair.first;
        int count=itempair.second;
        vector<int>newFreqSet=prefix;
        newFreqSet.push_back(itemId);
        results.push_back({newFreqSet,count});

        map<int,int>condFreqMap;
        vector<pair<vector<int>,int>>condPatterns;

        FPNode* node=headerTable[itemId].firstNode;
        while(node!=nullptr){
            vector<int>path;
            FPNode* parent=node->parent;

            while(parent && parent->itemId!=-1){
                path.push_back(parent->itemId);
                parent=parent->parent;
            }

            if(!path.empty()){
                int start=0;
                int end=path.size()-1;
                while(start<end){
                    int temp=path[start];
                    path[start]=path[end];
                    path[end]=temp;
                    start++;
                    end--;
                }
                condPatterns.push_back({path,node->count});
                for(int id:path){
                    condFreqMap[id]+=node->count;
                }
            }
            node=node->nodeLink;
        }
        FPNode* condRoot=new FPNode(-1);
        map<int,HeaderInfo>condHeaderTable;
        
        for(auto& pattern:condPatterns){
            vector<int>filteredPath;
            vector<int>originalPath=pattern.first;
            int pathCount=pattern.second;

            for(int id:originalPath){
                if(condFreqMap[id]>=min_sup){
                    filteredPath.push_back(id);
                }
            }

            manualSort(filteredPath,condFreqMap);

            if(!filteredPath.empty()){
                for(int id:filteredPath){
                    condHeaderTable[id].count+=pathCount;
                }
                insertTree(filteredPath,condRoot,condHeaderTable,pathCount);
            }
        }

        if(!condRoot->children.empty()){
            mineFP(condHeaderTable,min_sup,newFreqSet,results);
        }
    }
}

int main() {
    convertFile("INPUT.TXT", "output.txt");
    if(transactions==0){
        cerr<<"no transactions found . exiting\n";
        return 1;
    }
    cout<<"press 1 for running Apriori algorithm\n" 
    <<"press 2 for running Fp-growth algorithm\n"
    <<"press 3 for running Eclat algorithm\n\n";
    int users_desire;
    cin>>users_desire;
    int minimum_support_count=(int)ceil(transactions*minimum_support);
    cout<<"\nminimum support count: "<<minimum_support_count<<endl;
    if(users_desire==1){
        auto start=high_resolution_clock::now();
        map<vector<int>,int>all_itemset_supports;
        map<int,vector<vector<int>>>all_frequent_itemsets;
        cout<<"\nfinding frequent 1 itemsets(L1)...\n";
        all_frequent_itemsets[1]=findFrequent_1_Itemsets("output.txt",minimum_support_count,all_itemset_supports);
        for(const auto& itemset:all_frequent_itemsets[1]){
            printItemset(itemset);
            cout<<"(support: "<<all_itemset_supports[itemset]<<")\n";

        }
        int k=2;
        while(!all_frequent_itemsets[k-1].empty()){
            cout<<"\n ...pass..."<<k<<".....\n";
            cout<<"generating "<<k<<" itemset candidates (C"<<k<<")...\n";
            vector<vector<int>>Ck=generateCandidates(all_frequent_itemsets[k-1],k);
            if(Ck.empty()){
                cout<<"NO candidates generated. stopping\n";
                break;
            }
            cout<<"generated "<<Ck.size()<<" candidates\n";
            map<vector<int>,int>candidate_counts=countCandidateFrequencies("output.txt",Ck);
            cout<<"filtering for frequent "<<k<<"-itemsets(L"<<k<<")...\n";
            all_frequent_itemsets[k]=getFrequentItems(Ck,candidate_counts,minimum_support_count,all_itemset_supports);
            if(all_frequent_itemsets[k].empty()){
                cout<<"no frequent "<<k<<" itemsets found\n";
                break;
            }
            cout<<"found "<<all_frequent_itemsets[k].size()<<" frequent "<<k<<"itemsets\n";
            for(const auto& itemset:all_frequent_itemsets[k]){
                printItemset(itemset);
                cout<<"(support: "<<all_itemset_supports[itemset]<<")\n";
            }
            k++;
        }
        generateAndPrintRules(all_frequent_itemsets,all_itemset_supports);
        auto stop=high_resolution_clock::now();
        auto duration=duration_cast<milliseconds>(stop-start);
        cout<<"Execution time for Apriori: "<<duration.count()<<"ms\n";
        BuisnessAnalytics(all_itemset_supports,transactions);
        
    }

    else if(users_desire==2){
        //will use fp growth here

        string inputFile = "INPUT.TXT";
        
        ifstream in(inputFile);
        if (!in.is_open()) {
            cerr << "Error: " << inputFile << " not found!" << endl;
            return 1;
        }

        string line;
        int totalTransactions = 0;
        map<int, int> frequencyMap;

        while(getline(in, line)) {
            totalTransactions++;
            
            for(size_t i=0; i<line.length(); i++) {
                if(line[i] == ',' || line[i] == ':') line[i] = ' ';
            }
            
            stringstream ss(line);
            string word;
            
            vector<int> seenInTx; 

            while(ss >> word) {
                if(word[0] == 'I' || word[0] == 'i') {
                    int id = 0;
                    
                    try {
                        id = stoi(word.substr(1)) - 1;
                    } catch(...) { continue; }

                    bool seen = false;
                    for(size_t k=0; k<seenInTx.size(); k++) {
                        if(seenInTx[k] == id) seen = true;
                    }

                    if(!seen) {
                        frequencyMap[id]++;
                        seenInTx.push_back(id);
                    }
                }
            }
        }

        
        cout << "Transactions: " << totalTransactions << " | Min Sup: " << minimum_support_count << endl;

        map<int,HeaderInfo>headerTable;
        for(auto const& pair:frequencyMap){
            if(pair.second>=minimum_support_count){
                headerTable[pair.first].count=pair.second;
            }
        }

        in.clear();
        in.seekg(0, ios::beg);

        FPNode* root = new FPNode(-1); 

        while(getline(in, line)) {
            for(size_t i=0; i<line.length(); i++) {
                if(line[i] == ',' || line[i] == ':') line[i] = ' ';
            }

            stringstream ss(line);
            string word;
            vector<int> transaction;
            vector<int> seenInTx;

            while(ss >> word) {
                if(word[0] == 'I' ) {
                    try {
                        int id = stoi(word.substr(1)) - 1;
                        if(headerTable.count(id)) {
                    
                            bool seen = false;
                            for(size_t k=0; k<seenInTx.size(); k++) {
                                if(seenInTx[k] == id){
                                     seen = true;
                                }     
                            }
                            if(!seen) {
                                transaction.push_back(id);
                                seenInTx.push_back(id);
                            }
                        }
                    } catch (...) {}
                }
            }

            manualSort(transaction, frequencyMap);

            if(!transaction.empty()){
                insertTree(transaction,root,headerTable);
            }
        }
        in.close();

        int fpChoice;
        cout<<"\n======================\n";
        cout<<"\n FP-GROWTH MENU \n";
        cout<<"1. print fp-tree structure \n";
        cout<<"2. mine frequent itemsets \n";
        cout<<"0. exit \n";
        cout<<"enter choice: ";
        cin>>fpChoice;
        
        if(fpChoice==1){
            cout<<"\n--- FP Growth Tree ---\n";
            printTree(root,"",true);
        }
        else if(fpChoice==2){
            cout<<"\n---- Mining Frequent Itemsets ----\n";
            auto start=high_resolution_clock::now();

            vector<int>prefix;
            vector<pair<vector<int>,int>>results;

            mineFP(headerTable,minimum_support_count,prefix,results);
            auto stop=high_resolution_clock::now();
            auto duration=duration_cast<milliseconds>(stop-start);

            ManualSortresults(results);
            cout<<"Found "<<results.size()<<" frequent itemsets:\n";
            for(const auto&res :results){
                printItemset(res.first);
                cout<<" (support: "<<res.second<<")\n";
            }
            cout<<"\n-------------------------\n";
            cout<<"execution time for fp-growth mining: "<<duration.count()<<"ms\n";
            cout<<"--------------------------\n";

            cout<<"\n------------------------\n";
            cout<<"GENERATING ASSOCIATION RULES (FP GROWTH)\n";
            cout<<"\n------------------------\n";
            map<vector<int>,int>all_itemsets_supports;
            for(auto& res:results){
                vector<int>itemsets=res.first;
                my_sort(itemsets.begin(),itemsets.end());
                all_itemsets_supports[itemsets]=res.second;
            }

            cout<<"\n--- Strong Rules (min Confidence: "<<min_confidence*100<<"%)---\n";
            for(const auto& res:results){
                vector<int>itemset=res.first;
                if(itemset.size()>=2){
                    my_sort(itemset.begin(),itemset.end());
                    vector<int>antecedent;
                    generateRulesRecursive(itemset,antecedent,0,all_itemsets_supports);
                }
            }

            map<vector<int>,int>analyticsMap;
            for(auto&res: results){
                vector<int>itemsets=res.first;
                my_sort(itemsets.begin(),itemsets.end());
                analyticsMap[itemsets]=res.second;
            }
            BuisnessAnalytics(analyticsMap,totalTransactions);
        }
        return 0;

    }
    else if(users_desire==3){
        //will use  eclat here
    }
    
    return 0;
}