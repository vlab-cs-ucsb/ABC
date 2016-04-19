#include "DependencyChecker.h"

namespace Vlab {
namespace Solver {

using namespace SMT;

const int DependencyChecker::VLOG_LEVEL = 20;


DependencyChecker::DependencyChecker(SymbolTable_ptr symbol_table): symbol_table(symbol_table) {
}

DependencyChecker::~DependencyChecker() {
}

void DependencyChecker::start(){
	DVLOG(VLOG_LEVEL) << "Starting the Dependency Checker";
	db = redisConnect("localhost", 6379);
	if (not db||db->err) {
        redisFree(db);
        DVLOG(VLOG_LEVEL) << "ERROR CONNECTING!";
     }
	redisReply *reply;	
	//Change for the new version of components!
	for (auto& c: symbol_table->getComponents()){
		DVLOG(VLOG_LEVEL) << "Checking component " << c->toString();
		std::string st = c->toString();
		reply = (redisReply*)redisCommand(db,"GET %s",st.c_str());
		if (reply->str){
		  DVLOG(VLOG_LEVEL) << "A solution was found in the database:: " << reply->str;
		  symbol_table->incrementReuse();
		  c->setSolved(true);
		  if (reply->str == std::string("sat")){
		  	c->setSat(true);
		  }
		}
	}
	//Free the context 
	redisFree(db);

}





} //Vlab
} //Solver