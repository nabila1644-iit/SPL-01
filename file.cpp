#include<iostream>
#include<string>
#include<sstream>
#include<fstream>
#include<vector>

using namespace std;

int transactions = 0;

struct my_pair{
    int first;
    int second;
};

my_pair make_pair_custom(int first,int second){
    my_pair p;
    p.first=first;
    p.second=second;
    return p;
}

void convertFile(const string &inputFile, const string &outputFile) {
    ifstream in(inputFile);
    ofstream out(outputFile);
    string line;
    
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
}

int main() {
    convertFile("G:\\INPUT.TXT", "output.txt");
    
    
    vector<vector<int>> items_array;
    vector<int> item_count(5, 0);  
    ifstream in("output.txt");
    string line;

    int minimum_frequency=2;
    
    while(getline(in, line)) {
        vector<int> row(5, 0);  
        stringstream ss(line);
        string words;
        
        while(ss >> words) {
            if(words[0] == 'I' && words.length() > 1) {
                int item_index = words[1] - '1';  
                if(item_index >= 0 && item_index < 5) {
                    row[item_index]=1;
                    item_count[item_index]++;
                }
            }
        }
        items_array.push_back(row);
    }
    in.close();
   
    cout << "1 item frequencies" << endl;
    for(int i = 0; i < item_count.size(); i++) {
        cout << "I" << (i+1) << " = " << item_count[i] << endl;
    }

    vector<int>frequent_items;
    cout<<"1 item frequent items count\n";
    for(int i=0;i<item_count.size();i++){
        if(item_count[i]>=minimum_frequency){
            frequent_items.push_back(i);
            cout<<"I"<<(i+1)<<" = "<<item_count[i]<<"\n";
        }
    }

    vector<my_pair>pairs;
    for(int i=0;i<frequent_items.size();i++){
        for(int j=i+1;j<frequent_items.size();j++){
            pairs.push_back(make_pair_custom(frequent_items[i],frequent_items[j]));

        }
    }

    vector<int>pair_count(pairs.size(),0);
    for(int i=0;i<items_array.size();i++){
        for(int j=0;j<pairs.size();j++){
            int item1=pairs[j].first;
            int item2=pairs[j].second;
            if(items_array[i][item1]>0 && items_array[i][item2]>0){
                pair_count[j]++;
            }
        }
    }

    cout<<"2 item frequencies\n";
    for(int i=0;i<pairs.size();i++){
        int item1=pairs[i].first;
        int item2=pairs[i].second;
        cout<<"(I"<<(item1+1)<<",I"<<(item2+1)<<") = "<<pair_count[i]<<"\n";
    }

    cout<<"2 item frequent items count\n";
    for(int i=0;i<pairs.size();i++){
        
        if(pair_count[i]>=minimum_frequency){
            int item1=pairs[i].first;
            int item2=pairs[i].second;
            cout<<"(I"<<(item1+1)<<",I"<<(item2+1)<<") = "<<pair_count[i]<<"\n";
        }
    }

    
    

    
    return 0;
}