#include<iostream>
#include<sstream>
#include<queue>
#include<fstream>
#include<string>
#include<list>
#include<algorithm>
#include<stdlib.h>
#include <vector>
#include<deque>
#include<map>
using namespace std;

string GetPredicateName(string predicate);
string GetFirstArgument(string predicate);
string GetSecondArgument(string predicate);
vector<string> GetPremisePredicates(string clause);
string GetConclusionPredicate(string clause);
vector<string> ListContains(deque<Predicate*> List,Predicate* predicate,vector<string> theta,deque<int> &clauseNum);
int Contains(deque<Predicate*> List,Predicate* predicate,vector<string> theta);
vector<string> infer(Predicate* predicate,vector<string> theta,int d);

class Predicate{
private:
	string value;
	string predicateName;
	string firstArg;
	string secondArg;
	int clauseNum;
public:

	Predicate(){
	}

	Predicate(string v,int cn, string pn, string fa, string sa){
		value = v;
		clauseNum = cn;
		predicateName = pn;
		firstArg = fa;
		secondArg = sa;
	}

	string GetValue(){
		return value;
	}

	string GetPredicateName(){
		return predicateName;
	}
	string GetFirstArgument(){
		return firstArg;
	}
	string GetSecondArgument(){
		return secondArg;
	}

	void SetFirstArgument(string fa){
		firstArg = fa;
	}
	void SetSecondArgument(string sa){
		secondArg = sa;
	}
	int GetClauseNum(){
		return clauseNum;
	}
};


Predicate *predicate;
deque<Predicate*> PremiseList;
deque<Predicate*> FactList;
deque<Predicate*> ConclusionList;
vector<string> arrClauses;

string GetPredicateName(string predicate){
	string implySymbol("(");
	size_t pos = predicate.find(implySymbol);
	predicate.erase(pos , predicate.length());
	return predicate;
}

string GetFirstArgument(string predicate){
	size_t obpos = predicate.find("(");
	predicate.erase(0, obpos+1);
	size_t cpos = predicate.find(",");

	if(cpos == std::string::npos){
		cpos = predicate.find(")");
		predicate.erase(cpos,predicate.length());
	}
	else{
		predicate.erase(cpos,predicate.length());
	}
	return predicate;
}

string GetSecondArgument(string predicate){
	size_t cpos = predicate.find(",");
	if(cpos!=std::string::npos){
		predicate.erase(0, cpos+1);
		size_t cbpos = predicate.find(")");
		predicate.erase(cbpos,predicate.length());
		return predicate;
	}
	else{
		return "";
	}
}

vector<string> GetPremisePredicates(string clause){
	vector<string> predicates; 
	string implySymbol("=>");
	string andSymbol("&");
	size_t ifound = clause.find(implySymbol);

	if (ifound!=std::string::npos){
		clause.erase(ifound , clause.length());
		size_t pos = 0;
		std::string token;
		while ((pos = clause.find(andSymbol)) != std::string::npos) {
			token = clause.substr(0, pos);
			predicates.push_back(token);
			clause.erase(0, pos + andSymbol.length());
		}
		predicates.push_back(clause);
	}
	else
		predicates.push_back(clause);

	return predicates;

}

string GetConclusionPredicate(string clause){
	string implySymbol("=>");
	size_t ifound = clause.find(implySymbol);

	if (ifound!=std::string::npos){
		return clause.erase(0, ifound + implySymbol.length());
	}
	else{
		return "";
	}

}


vector<string> ListContains(deque<Predicate*> List,Predicate* predicate,vector<string> theta,deque<int> &clauseNum){

	stringstream convert;

	for(int i=0;i<List.size();i++){

		if(predicate->GetPredicateName() == List[i]->GetPredicateName()){
			if(predicate->GetFirstArgument() == List[i]->GetFirstArgument() &&  predicate->GetSecondArgument() == List[i]->GetSecondArgument()){
				theta.push_back("NOX");
				clauseNum.push_back(List[i]->GetClauseNum()-1);
			}
			else if(predicate->GetFirstArgument() == "x" &&  predicate->GetSecondArgument() == List[i]->GetSecondArgument()){
				theta.push_back(List[i]->GetFirstArgument());
				clauseNum.push_back(List[i]->GetClauseNum()-1);
			}
			else if(predicate->GetFirstArgument() == List[i]->GetFirstArgument() &&  predicate->GetSecondArgument() == "x"){
				theta.push_back(List[i]->GetSecondArgument());
				clauseNum.push_back(List[i]->GetClauseNum()-1);
			}
			else if(List[i]->GetFirstArgument() == "x" &&  predicate->GetSecondArgument() == List[i]->GetSecondArgument()){
				theta.push_back(predicate->GetFirstArgument());
				clauseNum.push_back(List[i]->GetClauseNum()-1);
			}
			else if(predicate->GetFirstArgument() == List[i]->GetFirstArgument() &&  List[i]->GetSecondArgument() == "x"){
				theta.push_back( predicate->GetSecondArgument());
				clauseNum.push_back(List[i]->GetClauseNum()-1);
			}
		}

	}
	return theta;
}

int Contains(deque<Predicate*> List,Predicate* predicate,vector<string> theta){

	for(int i=0;i<List.size();i++){

		if(predicate->GetPredicateName() == List[i]->GetPredicateName()){
			if(predicate->GetFirstArgument() == List[i]->GetFirstArgument() &&  predicate->GetSecondArgument() == List[i]->GetSecondArgument()){
				return 1;
			}

		}

	}

	return 0;

}

vector<string> infer(Predicate* predicate,vector<string> theta,int d){
	
	deque<Predicate*> entailList;
	deque<Predicate*> entailedList;
	Predicate* ppredicate;
	vector<string> premisePredicates;
	vector<Predicate*> p;
	vector<string> thetaF; 
	vector<string> thetaC;
	vector<string> thetaM; 
	vector<string> thetaPr; 
	vector<string> thetaT;
	vector<string> thetaTBP;
	vector<string> thetaCC;
	vector<string>::iterator last;
	int flag = 0;
	deque<int> clauseNum;
	deque<int> fclauseNum;
	string spredicate;
	int UNIFIED = 0;

	entailList.push_back(predicate);
	
	while(entailList.size() != 0){
		predicate = entailList.front();
		entailList.pop_front();
		entailedList.push_back(predicate);

		if(d == 0 || d == 2){
			theta = ListContains(FactList,predicate,theta,fclauseNum);
		}

		if(d == 1 || d == 2){
			if(theta.size() == 0){
				thetaCC = ListContains(ConclusionList,predicate,theta,clauseNum);
	
				for(int i=0;i<clauseNum.size();i++){
					spredicate = GetConclusionPredicate(arrClauses[clauseNum[i]]);
					if((GetFirstArgument(spredicate) == "x" && GetFirstArgument(spredicate) != predicate->GetFirstArgument()) || (GetSecondArgument(spredicate) == "x" && GetSecondArgument(spredicate) != predicate->GetSecondArgument())){
							
						theta.clear();
						theta.push_back(thetaCC[i]);
							
					}

					if(GetFirstArgument(spredicate) != "x" && GetFirstArgument(spredicate) != "x"){
							UNIFIED = 1;
							thetaTBP.push_back(thetaCC[i]);
							theta.clear();
					}
					
					premisePredicates = GetPremisePredicates(arrClauses[clauseNum[i]]);

					for(int j=0;j<premisePredicates.size();j++){
						thetaT.clear();
						if(j != 0 && theta.size() == 0){
							break;
						}

						ppredicate = new Predicate(premisePredicates[j],j+1, GetPredicateName(premisePredicates[j]),GetFirstArgument(premisePredicates[j]),GetSecondArgument(premisePredicates[j]));
						
						if(!Contains(entailedList,ppredicate,theta)){
							if(theta.size() == 0){
								theta = infer(ppredicate,theta,0);
								thetaC = infer(ppredicate,thetaC,1);
								if(thetaC.size() != 0 && theta.size() != 0){
									for(int x=0;x<thetaC.size();x++){
										for(int y=0;y<theta.size();y++){
											if(thetaC[x] == theta[y])
												flag=1;
										}
										if (!flag) {
											theta.push_back(thetaC[x]);
										}
										flag = 0;
									}
								}
								if(thetaC.size() != 0 && theta.size() == 0){
									theta = thetaC;
								}
								if(thetaC.size() == 0 && theta.size() == 0){
									break;
								}
								
							}else{
								for(int z=0;z<theta.size();z++){
									thetaF.clear();
									thetaC.clear();
									string sub = "";
									if(ppredicate->GetFirstArgument() == "x"){
										sub = theta[z];
										ppredicate->SetFirstArgument(sub);
										thetaF = infer(ppredicate,thetaF,0);
									
										if(thetaF.size()!=0){
											thetaT.push_back(sub);
										}

										if(thetaF.size() == 0){
											thetaC = infer(ppredicate,thetaC,1);
											if(thetaC.size()!=0){
												thetaT.push_back(sub) ;
											}
										}
										ppredicate->SetFirstArgument("x");
									}else if(ppredicate->GetSecondArgument() == "x") {
										sub = theta[z];
										ppredicate->SetSecondArgument(theta.back());										
										thetaF = infer(ppredicate,thetaF,0);
									
										if(thetaF.size()!=0){
											thetaT.push_back(sub);
										}

										if(thetaF.size() == 0){
											thetaC = infer(ppredicate,thetaC,1);
											if(thetaC.size()!=0){
												thetaT.push_back(sub) ;
											}
										}
										ppredicate->SetSecondArgument("x");
									}else{
										sub = theta[z];
										thetaF = infer(ppredicate,thetaF,0);
										if(thetaF.size()!=0){
											thetaT.push_back(sub);
										}

										if(thetaF.size() == 0){
											thetaC = infer(ppredicate,thetaC,1);
											if(thetaC.size()!=0){
												thetaT.push_back(sub) ;
											}
										}
									}
								}
								theta.clear();
								if(thetaT.size() != 0){
									for(int x=0;x<thetaT.size();x++){
										theta.push_back(thetaT[x]);
									}
								}else{
									break;
								}
							}	
						}
					}
					if(theta.size() != 0){
						if(UNIFIED){
							thetaPr.push_back(thetaTBP.back());
							UNIFIED = 0;
						}
						else{
							thetaPr.push_back(theta.back());
						}
					}
				}
			}
		}
	}
	if(theta.size() != 0){
		for(int x=0;x<theta.size();x++){
			for(int y=0;y<thetaPr.size();y++){
				if(theta[x] == thetaPr[y])
					flag=1;
				}
				if (!flag) {
				    thetaPr.push_back(theta[x]);
				}
				flag = 0;
		}
	}
	return thetaPr;
}

int main(){
	string query;
	string buffer;
	string clause;
	int numClauses;
	vector<string> premisePredicates;
	vector<string> theta;

	string conclusionPredicate;
	string predicateName;
	string firstArgument;
	string secondArgument;
	std::map< string,vector<Predicate*> > PredicateMap;
	ifstream myFile("input.txt");

	getline(myFile,query);
	getline(myFile,buffer);

	istringstream nc(buffer);
	nc >> numClauses;

	for(int i=0;i<numClauses;i++){
		getline(myFile,clause);
		arrClauses.push_back(clause);
		premisePredicates = GetPremisePredicates(clause);
		conclusionPredicate = GetConclusionPredicate(clause);
		
		/*Build Premise List*/
		if(premisePredicates.size() == 1 && conclusionPredicate == ""){

			firstArgument = GetFirstArgument(premisePredicates[0]);
			secondArgument = GetSecondArgument(premisePredicates[0]);
			predicateName =  GetPredicateName(premisePredicates[0]);
			predicate = new Predicate(premisePredicates[0],i+1,predicateName,firstArgument,secondArgument);
			FactList.push_back(predicate);

		}
		/*Build Fact List*/
		else{

			for(int j=0;j<premisePredicates.size();j++){
				firstArgument = GetFirstArgument(premisePredicates[j]);
				secondArgument = GetSecondArgument(premisePredicates[j]);
				predicateName =  GetPredicateName(premisePredicates[j]);
				predicate = new Predicate(premisePredicates[j],i+1,predicateName,firstArgument,secondArgument);
				PremiseList.push_back(predicate);
			}

		}
		/*Build Conclusion List*/
		if(conclusionPredicate != ""){

			firstArgument = GetFirstArgument(conclusionPredicate);
			secondArgument = GetSecondArgument(conclusionPredicate);
			predicateName =  GetPredicateName(conclusionPredicate);
			predicate = new Predicate(conclusionPredicate,i+1,predicateName,firstArgument,secondArgument);
			ConclusionList.push_back(predicate);
			conclusionPredicate = "";

		}
	}

	predicate = new Predicate(query,0,GetPredicateName(query),GetFirstArgument(query),GetSecondArgument(query));

	theta = infer(predicate,theta,2);
	
	ofstream out("output.txt");

	if(theta.size() != 0){
		out << "TRUE" << endl;
	}
	else{
		out << "FALSE" << endl;
	}
}
