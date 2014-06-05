//===- DetectMsp.cpp ----------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Example clang plugin which detects missing sequence points at expressions.
//
//===----------------------------------------------------------------------===//

#include "clang/Frontend/FrontendPluginRegistry.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/AST.h"
#include "clang/Frontend/CompilerInstance.h"
#include "llvm/Support/raw_ostream.h"
#include <map>
#include <stack>
#include <list>
#include <iostream>
#include <string.h>

// All unary operators.
#define UNARYOP_LIST()                          \
	OPERATOR(PostInc)   OPERATOR(PostDec)         \
OPERATOR(PreInc)    OPERATOR(PreDec)          \
OPERATOR(AddrOf)    OPERATOR(Deref)           \
OPERATOR(Plus)      OPERATOR(Minus)           \
OPERATOR(Not)       OPERATOR(LNot)            \
OPERATOR(Real)      OPERATOR(Imag)            \
OPERATOR(Extension)

// All binary operators (excluding compound assign operators).
#define BINOP_LIST() \
	OPERATOR(PtrMemD)              OPERATOR(PtrMemI)    \
OPERATOR(Mul)   OPERATOR(Div)  OPERATOR(Rem)        \
OPERATOR(Add)   OPERATOR(Sub)  OPERATOR(Shl)        \
OPERATOR(Shr)                                       \
\
OPERATOR(LT)    OPERATOR(GT)   OPERATOR(LE)         \
OPERATOR(GE)    OPERATOR(EQ)   OPERATOR(NE)         \
OPERATOR(And)   OPERATOR(Xor)  OPERATOR(Or)         \
OPERATOR(LAnd)  OPERATOR(LOr)                       \
\
OPERATOR(Assign)                                    \
OPERATOR(Comma)

// All compound assign operators.
#define CAO_LIST()                                                      \
	OPERATOR(Mul) OPERATOR(Div) OPERATOR(Rem) OPERATOR(Add) OPERATOR(Sub) \
OPERATOR(Shl) OPERATOR(Shr) OPERATOR(And) OPERATOR(Or)  OPERATOR(Xor)

#define TRY_TO(CALL_EXPR) \
	do { if (!getDerived().CALL_EXPR) return false; } while (0)

#include <stdio.h>
using namespace clang;
using namespace std;

namespace {

#define EVT_STATE_R		1
#define EVT_STATE_W		2
#define EVT_STATE_SW		3
#define EVT_STATE_UNDEF		4
#define RVE_OR 			"#OR"
#define EOL 			"#end"


	class evt {
		private:
			char id[256];
			int state;
		public:
			evt(char* id_, int state_) {
				strcpy(id, id_);
				state = state_;
			}

			void setState(int state_) { state = state_; }
			int getState() { return state; }
			char* getId() { return id; }
	};


	void orExpend(char* op, char a[][256], char b[][256]){
		int newSize = 1, i=1, j=1;
		//char** newList = (char**)malloc(sizeof(char)*256*256);	
		char newList[256][256];

		if(strcmp(a[0], RVE_OR)==0 && strcmp(a[1], EOL)==0) {
			strcpy(a[0], EOL);
			printf("INVALID RVE IN RVALUE");
			return;
		}

		while(true){
			while(true){
				strcpy(newList[newSize], op);
				strcat(newList[newSize], " ");
				strcat(newList[newSize], a[i]);
				strcat(newList[newSize], " ");
				strcat(newList[newSize], b[j]);
				j++;
				newSize++;
				if(strcmp(b[j], EOL)==0) break;
			}		
			i++;		
			if(strcmp(b[i], EOL)==0) break;
		}
		//a = newList;
		strcpy(newList[newSize], EOL);

		i=0;
		while(true){
			strcpy(a[i], newList[i]);
			i++;
			if(strcmp(newList[i], EOL)==0) break;
		}
		strcpy(a[i], EOL);
	}

	void binJoin(const char* op, char a[][256], char b[][256]){
		int newSize = 1, i=1, j=1;
		//char** newList = (char**)malloc(sizeof(char)*256*256);	
		char newList[256][256];
		if(strcmp(a[0], EOL)==0 || strcmp(b[0], EOL)==0) {
			strcpy(a[0], EOL);
			printf("NO VALUE IN RVALUE");
			return;
		}
		if (strcmp(a[0], RVE_OR)==0 && strcmp(b[0], RVE_OR)==0){		
			if(strcmp(a[1], EOL)==0) {
				strcpy(a[0], EOL);
				printf("INVALID RVE IN RVALUE");
				return;
			}

			strcpy(newList[0], RVE_OR);
			while(true){
				while(true){
					if(strcmp(b[j], EOL)==0) break;
					strcpy(newList[newSize], op);
					strcat(newList[newSize], " ");
					strcat(newList[newSize], a[i]);
					strcat(newList[newSize], " ");
					strcat(newList[newSize], b[j]);
					j++;
					newSize++;		
				}		
				i++;		
				if(strcmp(a[i], EOL)==0) break;
			}
			//a = newList;
			strcpy(newList[newSize], EOL);

			i=0;
			while(true){
				strcpy(a[i], newList[i]);
				i++;
				if(strcmp(newList[i], EOL)==0) break;
			}
			strcpy(a[i], EOL);
		}else if (strcmp(a[0], RVE_OR)!=0 && strcmp(b[0], RVE_OR)==0){
			char tmp[256];
			strcpy(tmp, a[0]);
			strcpy(a[0], RVE_OR);
			i=1;
			while(true){
				strcpy(a[i], op);
				strcat(a[i], " ");
				strcat(a[i], tmp);
				strcat(a[i], " ");
				strcat(a[i], b[i]);
				i++;
				if(strcmp(b[i], EOL)==0) break;
			}
			strcpy(a[i], EOL);
		}else if (strcmp(a[0], RVE_OR)==0 && strcmp(b[0], RVE_OR)!=0){
			char tmp[256];		
			strcpy(a[0], RVE_OR);
			i=1;
			while(true){
				strcpy(tmp, a[i]);
				strcpy(a[i], op);
				strcat(a[i], " ");
				strcat(a[i], tmp);
				strcat(a[i], " ");
				strcat(a[i], b[0]);
				i++;
				if(strcmp(a[i], EOL)==0) break;
			}
			strcpy(a[i], EOL);
		}else if (strcmp(a[0], RVE_OR)!=0 && strcmp(b[0], RVE_OR)!=0){
			char tmp[256];		
			strcpy(tmp, a[0]);
			strcpy(a[0], op);
			strcat(a[0], " ");
			strcat(a[0], tmp);
			strcat(a[0], " ");
			strcat(a[0], b[0]);
		}
	}

	void condJoin(char a[][256], char b[][256]){
		char tmpList[256][256];

		strcpy(tmpList[0], RVE_OR);
		int i=1, j=0;
		while(true){
			if(strcmp(a[j], RVE_OR)==0) continue;
			strcpy(tmpList[i], a[j]);
			i++;
			j++;
			if(strcmp(a[j], EOL)==0) break;
		}	
		j=0;
		while(true){
			if(strcmp(b[j], RVE_OR)==0) continue;
			strcpy(tmpList[i], b[j]);
			i++;
			j++;
			if(strcmp(b[j], EOL)==0) break;
		}
		strcpy(tmpList[i], EOL);

		i=0;
		while(true){
			strcpy(a[i], tmpList[i]);
			i++;
			if(strcmp(tmpList[i], EOL)==0) break;
		}
		strcpy(a[i], EOL);
	}

	class Rvalue{
		private:
			list<evt*>* evtList;
		public:
			char rv_e[256][256]; // Expression

			Rvalue() {
				rv_e[0][0] = '\0';
				strcpy(rv_e[1], EOL);
				evtList = new list<evt*>();
			}

			Rvalue(char* rve, evt* e){
				strcpy(rv_e[0], rve);
				strcpy(rv_e[1], EOL);
				evtList = new list<evt*>();
				evtList->push_back(e);
			}

			Rvalue(char* rve, list<evt*>* list){
				strcpy(rv_e[0], rve);
				strcpy(rv_e[1], EOL);
				evtList = list;
			}

			void setValue(const char* rve) {
				strcpy(rv_e[0], rve);
			}

			void appendValue(const char* rve1, const char* rve2) {
				strcat(rv_e[0], rve1);
				strcat(rv_e[0], rve2);
			}

			char* getValue() {
				return rv_e[0];
			}

/*
			char[][256] getValueList(){
				return rv_e;
			}			
*/
			void setValueList(int index, const char* value){
				strcpy(rv_e[index], value);
			}

			void setList(list<evt*>* list) { evtList = list; }
			list<evt*>* getList(){return evtList;}

			void appendEvent(evt* e) {
				evtList->push_back(e);
			}

			void clean() {
			}
	};

	class Lvalue{
		private:
			char id[256]; // Variable name
			Rvalue* rv;
		public:
			Lvalue() {
				id[0] = '\0';
				rv = NULL;
			}

			Lvalue(char* i, Rvalue* rvalue){
				strcpy(id, i);
				rv = rvalue;
			}

			void setId(const char* i) {
				strcpy(id, i);
			}

			char* getId() { return id; }
			Rvalue* getRvalue() {return rv;}

			list<evt*>* getList() {
				if(rv == NULL) {
					return new list<evt*>();
				} else {
					return rv->getList();
				}
			}

			void setRvalue(Rvalue* rvalue){rv = rvalue;}

			int isId() {
				if(id[0] == '\0') {
					if(rv != NULL) {
						return 2;
					} else {
						return -1;
					}
				} else {
					if(rv != NULL) {
						return -1;
					} else {
						return 1;
					}
				}
			}

			void clean() {
				if(rv != NULL) {
					rv->clean();
					delete(rv);
				}
			}
	};

	// TYPE in NODE
#define LVALUE 1
#define RVALUE 2

	class Node{
		private:
			unsigned kind;		//Kind of the node (unary ,binary etc)
			unsigned opcode;	// Operator code
			Rvalue* rv;		//link to R-value object
			Lvalue* lv;		// link to the L-value Object
			int type; 		// RVALUE | LVALUE | 
			SourceLocation loc;	// loctaion in the source program

		public:
			Node() {		//initialization 
				kind = 0;
				opcode = 0;
				rv = NULL;
				lv = NULL;
			}

			void setKind(unsigned k) { kind = k; } 
			void setOpcode(unsigned k) { opcode = k; } 

			unsigned getKind() { return kind; } 
			unsigned getOpcode() { return opcode; } 

			void setRvalue(Rvalue* rvalue){rv = rvalue;}
			void setLvalue(Lvalue* lvalue){lv = lvalue;}
			Rvalue* getRvalue(){return rv;}
			Lvalue* getLvalue(){
				return lv;
			}

			void setType(int k){ type = k; }
			int getType(){ return type; }

			SourceLocation getSLoc() { return loc; }
			void setSLoc(SourceLocation loc_) { loc = loc_; }

			void cleanLvalue() {
				lv->clean();
				delete(lv);
				lv = NULL;
			}
	};


	class DetectMspConsumer : public ASTConsumer,
	public RecursiveASTVisitor<DetectMspConsumer> {
		private:
			CompilerInstance &CI;
			//  std::map<unsigned int, Value*> Env;
			stack<Node*> nodestack;
			stack<Node*> resultstack;

		public:
			DetectMspConsumer(CompilerInstance &ci) : CI(ci) {}

			void emitWarning(SourceLocation loc, const char* error) {
				FullSourceLoc full(loc, CI.getSourceManager());
				Diagnostic &Diags = CI.getDiagnostics();
				unsigned id = Diags.getCustomDiagID(Diagnostic::Error,error);
				DiagnosticBuilder B = Diags.Report(full, id);
				B.Emit();

				while(nodestack.empty() == false)
					nodestack.pop();

				while(resultstack.empty() == false)
					resultstack.pop();

			}

#define OPERATOR(NAME)                                           \
			bool VisitUnary##NAME(UnaryOperator *S) {						 \
				Node* n = new Node();\
				n->setKind(1);\
				n->setOpcode(S->getOpcode());\
				n->setSLoc(S->getLocStart());\
				nodestack.push(n);							 \
		      return true;												 \
			}

			UNARYOP_LIST()
#undef OPERATOR

#define GENERAL_BINOP_FALLBACK(NAME, BINOP_TYPE)                \
				bool VisitBin##NAME(BINOP_TYPE *S) { 	\
					Node* n = new Node();\
					n->setKind(2);\
					n->setOpcode(S->getOpcode());\
					n->setSLoc(S->getLocStart());\
					nodestack.push(n);							 \
					return true;								\
				}

#define OPERATOR(NAME) GENERAL_BINOP_FALLBACK(NAME, BinaryOperator)
				BINOP_LIST()
#undef OPERATOR

#define OPERATOR(NAME) \
				GENERAL_BINOP_FALLBACK(NAME##Assign, CompoundAssignOperator)

				CAO_LIST()
#undef OPERATOR
#undef GENERAL_BINOP_FALLBACK
                             	list<evt*>* WtoSW(list<evt*>* evt_list){  // w to sw set the state as sw for each having w
					list<evt*>::iterator it;
					it = evt_list->begin();
					
					while(it!=evt_list->end()){
						if((*it)->getState() == EVT_STATE_W)
							(*it)->setState(EVT_STATE_SW);
						it++;
					}
					return evt_list;
				}
					
				list<evt*>* merge_seq(list<evt*>* evt1, list<evt*>* evt2){
					list<evt*>* rst_evt = new list<evt*>();
					list<evt*>::iterator it1, it2;
					it1 = evt1->begin();
					it2 = evt2->begin();
					if(it1 == evt1->end())
						return evt2;
					if(it2 == evt2->end())
						return evt1;
					if((*it1)->getState() == EVT_STATE_UNDEF) {
						return evt1;
					}

					if((*it2)->getState() == EVT_STATE_UNDEF) {
						return evt2;
					}

					bool exist;
					while(it1!=evt1->end()){
						exist = false;
						it2 = evt2->begin();
						while(it2!=evt2->end()){
							if(strcmp((*it1)->getId(), (*it2)->getId())==0){
								//table of merge seq rules
								if((*it1)->getState() == EVT_STATE_R){
									switch((*it2)->getState()){
										case EVT_STATE_R:
											rst_evt->push_back(*it1); //R
											break;
										case EVT_STATE_SW:
											rst_evt->push_back(*it2);//SW
											break;
										case EVT_STATE_W:
											rst_evt->push_back(*it2); //W
											break;
									}
								}else if((*it1)->getState() == EVT_STATE_SW){
									switch((*it2)->getState()){
										case EVT_STATE_R:
											rst_evt->push_back(*it1); //SW
										case EVT_STATE_SW:
											rst_evt->push_back(*it1); //SW
											break;
										case EVT_STATE_W:
											rst_evt->push_back(*it2); //W
											break;
									}
								}else if((*it1)->getState() == EVT_STATE_W){
									switch((*it2)->getState()){
										case EVT_STATE_R:
											rst_evt->push_back(*it1); //w
											break;
										case EVT_STATE_SW:
											rst_evt->push_back(*it1); //W
											break;
										case EVT_STATE_W:
											rst_evt->push_back(*it1); //W
											break;
									}
								}

								evt2->erase(it2);
								exist = true;
								break;
							}
							it2++;
						}
						if(!exist)
							rst_evt->push_back(*it1);
						it1++;
					}

					it2 = evt2->begin();
					while(it2 != evt2->end()){
						rst_evt->push_back(*it2);
						it2++;
					}

					return rst_evt;
				}

			list<evt*>* merge_ordered(list<evt*>* evt1, list<evt*>* evt2){
				list<evt*>* rst_evt = new list<evt*>();
				list<evt*>::iterator it1, it2;
				it1 = evt1->begin();
				it2 = evt2->begin();
				if(it1 == evt1->end())
					return evt2;
				if(it2 == evt2->end())
					return evt1;

				if((*it1)->getState() == EVT_STATE_UNDEF) {
					return evt1;
				}

				if((*it2)->getState() == EVT_STATE_UNDEF) {
					return evt2;
				}

				bool exist;
				while(it1!=evt1->end()){
					exist = false;
					it2 = evt2->begin();
					while(it2!=evt2->end()){
						if(strcmp((*it1)->getId(), (*it2)->getId())==0){
							//table For Merge Ordered events rules
							if((*it1)->getState() == EVT_STATE_R){
								switch((*it2)->getState()){
									case EVT_STATE_R:
										rst_evt->push_back(*it1);
										break;
									case EVT_STATE_SW:
									case EVT_STATE_W:
										rst_evt->push_back(*it2);
										break;
								}
							}else if((*it1)->getState() == EVT_STATE_SW){
								switch((*it2)->getState()){
									case EVT_STATE_R:
									case EVT_STATE_SW:
										rst_evt->push_back(*it1);
										break;
									case EVT_STATE_W:
										rst_evt->push_back(*it2);
										break;
								}
							}else if((*it1)->getState() == EVT_STATE_W){
								switch((*it2)->getState()){
									case EVT_STATE_R:
									case EVT_STATE_SW:
									case EVT_STATE_W:
										(*it1)->setState(EVT_STATE_UNDEF);
										rst_evt->push_front(*it1);
										return rst_evt;
										break;
								}
							}

							evt2->erase(it2);
							exist = true;
							break;
						}
						it2++;
					}
					if(!exist)
						rst_evt->push_back(*it1);
					it1++;
				}

				it2 = evt2->begin();
				while(it2 != evt2->end()){
					rst_evt->push_back(*it2);
					it2++;
				}

				return rst_evt;
			}

			list<evt*>* merge_unordered(list<evt*>* evt1, list<evt*>* evt2){
				list<evt*>* rst_evt = new list<evt*>();
				list<evt*>::iterator it1, it2;
				it1 = evt1->begin();
				it2 = evt2->begin();
				if(it1 == evt1->end())
					return evt2;
				if(it2 == evt2->end())
					return evt1;
				if((*it1)->getState() == EVT_STATE_UNDEF) {
					return evt1;
				}

				if((*it2)->getState() == EVT_STATE_UNDEF) {
					return evt2;
				}

				bool exist;
				while(it1!=evt1->end()){
					exist = false;
					it2 = evt2->begin();
					while(it2!=evt2->end()){
						if(strcmp((*it1)->getId(), (*it2)->getId())==0){
							//table
							if((*it1)->getState() == EVT_STATE_R){
								switch((*it2)->getState()){
									case EVT_STATE_R:
										rst_evt->push_back(*it1);
										break;
									case EVT_STATE_SW:
									case EVT_STATE_W:
										(*it1)->setState(EVT_STATE_UNDEF);
										rst_evt->push_front(*it1);
										return rst_evt;
										break;
								}
							}else if((*it1)->getState() == EVT_STATE_SW){
								switch((*it2)->getState()){
									case EVT_STATE_R:
									case EVT_STATE_SW:
									case EVT_STATE_W:
										(*it1)->setState(EVT_STATE_UNDEF);
										rst_evt->push_front(*it1);
										return rst_evt;
										break;
								}
							}else if((*it1)->getState() == EVT_STATE_W){
								switch((*it2)->getState()){
									case EVT_STATE_R:
									case EVT_STATE_SW:
									case EVT_STATE_W:
										(*it1)->setState(EVT_STATE_UNDEF);
										rst_evt->push_front(*it1);
										return rst_evt;
										break;
								}
							}

							evt2->erase(it2);
							exist = true;
							break;
						}
						it2++;
					}
					if(!exist)
						rst_evt->push_back(*it1);
					it1++;
				}

				it2 = evt2->begin();
				while(it2 != evt2->end()){
					rst_evt->push_back(*it2);
					it2++;
				}
				return rst_evt;
			}

			bool VisitStmt(Stmt *S) { return true; }

			bool VisitDeclRefExpr(DeclRefExpr *E) {
				Node* n = new Node();
				n->setKind(3);
				n->setType(LVALUE);
				n->setSLoc(E->getLocStart());
				Lvalue *lv = new Lvalue();
				std::string e = E->getNameInfo().getName().getAsString();
				lv->setId(e.c_str());
				n->setLvalue(lv);
				nodestack.push(n);							 
				return true;
			}

			/*
			   bool VisitType(Type *T) { return true; }

#define ABSTRACT_TYPE(CLASS, BASE)
#define TYPE(CLASS, BASE) \
bool Visit##CLASS##Type(CLASS##Type *T) {

return true;
}
#include "clang/AST/TypeNodes.def"

bool VisitTypeLoc(TypeLoc TL) { return true; }
bool VisitQualifiedTypeLoc(QualifiedTypeLoc TL) { return true; }
bool VisitUnqualTypeLoc(UnqualTypeLoc TL) { return true; }

#define ABSTRACT_TYPELOC(CLASS, BASE)
#define TYPELOC(CLASS, BASE) \
bool Visit##CLASS##TypeLoc(CLASS##TypeLoc TL) { return true; }
#include "clang/AST/TypeNodes.def"
			 */
bool VisitDecl(Decl *D) { return true; }

/*
   bool VisitNamedDecl(NamedDecl *D) {
   Node* n = new Node();
   n->setKind(3);
   n->setId(D->getIdentifier()->getNameStart());
   nodestack.push(n);							 
   return true;
   }
 */

Rvalue* lvToRv(Node* n, Lvalue* lv){
	Rvalue* rv = new Rvalue();
	if (lv->getId()!=NULL && lv->getId()[0]!='\0'){
		// lv->rv[(lvalue id)] = (rvalue id (R id))
		char tmpId[256];
		strcpy(tmpId, lv->getId());

		rv->setValue(tmpId);								
		evt* tmpEvt = new evt(tmpId, EVT_STATE_R);
		rv->getList()->push_back(tmpEvt);
		if(lv->getRvalue()!=NULL)
			//printf("$$$$$$ %s\n", lv->getRvalue()->getValue());
		return rv;
	}else{
		if (lv->getRvalue()->getList()->size() == 0){ 
			// lv->rv[(lvalue rv0)]
			rv = new Rvalue();
			rv->setValue(lv->getRvalue()->getValue());

			if (strcmp(rv->rv_e[0], RVE_OR)==0){
				int i=1;
				while(strcmp(lv->getRvalue()->rv_e[i], EOL)!=0){
					strcpy(rv->rv_e[i], lv->getRvalue()->rv_e[i]);
					i++;
				}
				strcpy(rv->rv_e[i], EOL);
			}

			if (strcmp(rv->rv_e[0], RVE_OR)!=0){
				evt* tmpEvt = new evt(lv->getRvalue()->getValue(), EVT_STATE_R);
				rv->getList()->push_back(tmpEvt);
			}
	      else{
				list<evt*>* tmpList = new list<evt*>();
				int i=1;
				while(strcmp(lv->getRvalue()->rv_e[i], EOL)!=0){
					evt* tmpEvt = new evt(lv->getRvalue()->rv_e[i], EVT_STATE_R);
					tmpList->push_back(tmpEvt);
					i++;
				}
				rv->setList(tmpList);
			}
			return rv;
		}else if (lv->getRvalue()->getList()->size() > 0){ 
			//lv->rv[(lvalue (rvalue rv-e ets))]
			rv = new Rvalue();
			rv->setValue(lv->getRvalue()->getValue());

			if (strcmp(rv->rv_e[0], RVE_OR)==0){
				int i=1;
				while(strcmp(lv->getRvalue()->rv_e[i], EOL)!=0){
					strcpy(rv->rv_e[i], lv->getRvalue()->rv_e[i]);
					i++;
				}
				strcpy(rv->rv_e[i], EOL);
			}

			list<evt*>* tmpList = new list<evt*>();
			if (strcmp(rv->rv_e[0], RVE_OR)!=0){
				evt* tmpEvt = new evt(lv->getRvalue()->getValue(), EVT_STATE_R);
				tmpList->push_back(tmpEvt);
			}
			else{
				int i=1;
				while(strcmp(lv->getRvalue()->rv_e[i], EOL)!=0){
					evt* tmpEvt = new evt(lv->getRvalue()->rv_e[i], EVT_STATE_R);
					tmpList->push_back(tmpEvt);
					i++;
				}
			}

			list<evt*>* mo = merge_ordered(lv->getRvalue()->getList(), tmpList);

			list<evt*>::iterator it = mo->begin();
			it = mo->begin();
			if(it != mo->end()) {
				if((*it)->getState() == EVT_STATE_UNDEF) {
					emitWarning(n->getSLoc(), "MSP");
				}
			}

			rv->setList(mo);
			return rv;
		}else{
			printf("RVALUE HAS INVALID EVT LIST IN LV->RV");
			// not implemented rule: lv->rv[(lvalue (rvalue (OR et1, et2, ...) ets))]
		}
	}
	return rv;
}

bool TraverseCompoundStmt(CompoundStmt *S) {
	WalkUpFromCompoundStmt(S);

	Node* n;
	Node* n1,*n2, *n3;
	Node* newNode, *assignNode, *opNode;
	Lvalue* lv;
	Rvalue* rv;
	for (Stmt::child_range range = S->children(); range; ++range) {      
		TraverseStmt(*range);
		//printf("\n");
		while(!nodestack.empty()) {
			n = nodestack.top();
			nodestack.pop();

			//printf("%u %u %d %s\n", n->getKind(), n->getOpcode(), n->getType(), 
			//		(n->getKind()==3)?(n->getType()==1)?(n->getLvalue())->getId():(n->getRvalue())->getValue() : "");


			// KIND : 1, 2 = un/bi operator, 3 = variable, 4 = conditional operator(?)
			if(n->getKind() == 1) {
				int i=0;
				switch(n->getOpcode()) {
					case 0: //post INC
					case 1: //POST DEC
						// POST
						n2 = resultstack.top();
						resultstack.pop();

						lv = n2->getLvalue();

						if(lv->isId() == 1 || lv->getRvalue()==NULL) {
							n2->setRvalue(new Rvalue(lv->getId(), new evt(lv->getId(), EVT_STATE_W)));	
							n2->setType(RVALUE);
						} else if(lv->getRvalue()!=NULL) {
							list<evt*>* temp_evt = new list<evt*>();
							temp_evt->push_back(new evt(lv->getRvalue()->getValue(), EVT_STATE_W));	
							if(lv->getRvalue()->getList()->size()==0){
								n2->setRvalue(new Rvalue(lv->getRvalue()->getValue(), temp_evt));
								n2->setType(RVALUE);
							}else{
								n2->setRvalue( new Rvalue( lv->getRvalue()->getValue(), 
											(merge_ordered(lv->getRvalue()->getList(), temp_evt))));
								n2->setType(RVALUE);
							}
						}

						resultstack.push(n2);
						break;
					case 2:	// PRE INC
					case 3: // PRE DEC
						n3 = resultstack.top();
						resultstack.pop();

						if(n3->getType() == RVALUE) {
							rv = new Rvalue();
							rv->setValue(n3->getRvalue()->getValue());
							rv->setList(n3->getRvalue()->getList());
						}

						lv = new Lvalue();
						lv->setRvalue(rv);

						n1 = new Node();

						rv = new Rvalue();
						rv->setValue("1");
						n1->setType(RVALUE);
						n1->setKind(3);
						n1->setRvalue(rv);
						resultstack.push(n1);

						/*
						   n2->setType(LVALUE);
						   n2->setKind(3);
						   n2->setLvalue(lv);
						   resultstack.push(n2);
						 */
						resultstack.push(n3);

						n1 = new Node();
						n1->setSLoc(n->getSLoc());
						//cout << n->getSLoc() << endl;
						//emitWarning(n->getSLoc(), "xx");
						n1->setKind(2);
						if (n->getOpcode() == 2){
							n1->setOpcode(24);				
						}else if (n->getOpcode() == 3){
							n1->setOpcode(25);
						}
						nodestack.push(n1);
						break;

					case 4: //AddrOf
					case 5: //Deref
						n1 = resultstack.top();
						resultstack.pop();						

						if (n1 == NULL) printf("NOT ENOUGH OPERANDS FOR DEREF");

						if (n1->getType() == LVALUE){
							lv = n1->getLvalue();
							rv = lvToRv(n, lv);
							n1 = new Node();
							n1->setKind(3);
							n1->setType(RVALUE);
							n1->setRvalue(rv);
						}
						lv = new Lvalue();
						rv = new Rvalue();
						// need to implement binJoin function
						//rv->setValue(n1->getRvalue()->getValue());
						i=0;
						while(strcmp(n1->getRvalue()->rv_e[i], EOL)!=0){
							strcpy(rv->rv_e[i], n1->getRvalue()->rv_e[i]);
							i++;
						}
						strcpy(rv->rv_e[i], EOL);

						rv->setList(n1->getRvalue()->getList());
						i=0;
						while(strcmp(n1->getRvalue()->rv_e[i], EOL)!=0){
							if(strcmp(n1->getRvalue()->rv_e[i], RVE_OR)==0) {
								i++;
								continue;
							}
							evt* tmpEvt = new evt(n1->getRvalue()->rv_e[i], EVT_STATE_R);
							rv->appendEvent(tmpEvt);
							i++;
						}

						lv->setRvalue(rv);

						n = new Node();
						n->setType(LVALUE);
						n->setKind(3);						
						n->setLvalue(lv);
						resultstack.push(n);
						break;
					case 6: //Plus
						//For Plus, Minus, Not, LNot, rule not exist. Just add prefix at rv-e
						n1 = resultstack.top();
						resultstack.pop();						

						if (n1 == NULL) printf("NOT ENOUGH OPERANDS FOR UNARY PLUS");

						if (n1->getType() == LVALUE){
							rv = lvToRv(n, n1->getLvalue());
							n1 = new Node();
							n1->setKind(3);
							n1->setType(RVALUE);
							n1->setRvalue(rv);
						}
						rv = new Rvalue();
						// need to implement binJoin function *
						rv->appendValue("+", n1->getRvalue()->getValue());
						rv->setList(n1->getRvalue()->getList());

						n = new Node();
						n->setType(RVALUE);
						n->setKind(3);						
						n->setRvalue(rv);
						resultstack.push(n);
						break;
					case 7: //Minus
						n1 = resultstack.top();
						resultstack.pop();						

						if (n1 == NULL) printf("NOT ENOUGH OPERANDS FOR UNARY MINUS");

						if (n1->getType() == LVALUE){
							rv = lvToRv(n, n1->getLvalue());
							n1 = new Node();
							n1->setKind(3);
							n1->setType(RVALUE);
							n1->setRvalue(rv);
						}
						rv = new Rvalue();
						// need to implement binJoin function
						rv->appendValue("-", n1->getRvalue()->getValue());
						rv->setList(n1->getRvalue()->getList());

						lv->setRvalue(rv);

						n = new Node();
						n->setType(RVALUE);
						n->setKind(3);						
						n->setRvalue(rv);
						resultstack.push(n);
						break;
					case 8: //Not
						n1 = resultstack.top();
						resultstack.pop();						

						if (n1 == NULL) printf("NOT ENOUGH OPERANDS FOR UNARY NOT");

						if (n1->getType() == LVALUE){
							rv = lvToRv(n, n1->getLvalue());
							n1 = new Node();
							n1->setKind(3);
							n1->setType(RVALUE);
							n1->setRvalue(rv);
						}
						rv = new Rvalue();
						// need to implement binJoin function
						rv->appendValue("~", n1->getRvalue()->getValue());
						rv->setList(n1->getRvalue()->getList());

						lv->setRvalue(rv);

						n = new Node();
						n->setType(RVALUE);
						n->setKind(3);						
						n->setRvalue(rv);
						resultstack.push(n);
						break;
					case 9: //LNot
						n1 = resultstack.top();
						resultstack.pop();						

						if (n1 == NULL) printf("NOT ENOUGH OPERANDS FOR UNARY Logical Not");

						if (n1->getType() == LVALUE){
							rv = lvToRv(n, n1->getLvalue());
							n1 = new Node();
							n1->setKind(3);
							n1->setType(RVALUE);
							n1->setRvalue(rv);
						}
						rv = new Rvalue();
						// need to implement binJoin function
						rv->appendValue("!", n1->getRvalue()->getValue());
						rv->setList(n1->getRvalue()->getList());

						lv->setRvalue(rv);

						n = new Node();
						n->setType(RVALUE);
						n->setKind(3);						
						n->setRvalue(rv);
						resultstack.push(n);
						break;
					case 10: //Real   __real__(variable)->returns the real part of the comples number
						n1 = resultstack.top();
						resultstack.pop();
						
						if(n1 == NULL) printf("Not Enough operands for unary __real__ operator");
						
						if(n1->getType() == LVALUE){
							rv = lvToRv(n, n1->getLvalue());
							n1 = new Node();
							n1->setKind(3);
							n1->setType(RVALUE);
							n1->setRvalue(rv);
						}
						rv = new Rvalue();
						//Bin join function
						
						rv->appendValue("__real__", n1->getRvalue()->getValue());
						rv->setList(n1->getRvalue()->getList());
						lv->setRvalue(rv);
						
						
						n = new Node();	
						n->setType(RVALUE);;
						n->setKind(3);	
						n->setRvalue(rv);
						resultstack.push(n);
						break;				
					case 11: //Imag	  __imag__(variable)->return the imaginary part of the complex no.
						n1 = resultstack.top();
						resultstack.pop();
						
						if(n1 == NULL) printf("Not Enough operands for unary __imag__ operator");
						
						if(n1->getType() == LVALUE){
							rv = lvToRv(n, n1->getLvalue());
							n1 = new Node();
							n1->setKind(3);
							n1->setType(RVALUE);
							n1->setRvalue(rv);
						}
						rv = new Rvalue();
						//Bin join function
						
						rv->appendValue("__imag__", n1->getRvalue()->getValue());
						rv->setList(n1->getRvalue()->getList());
						lv->setRvalue(rv);
						
						
						n = new Node();	
						n->setType(RVALUE);;
						n->setKind(3);	
						n->setRvalue(rv);
						resultstack.push(n);
						break;	
					case 12: //Extension
						break;
				}
			} else if(n->getKind() == 2) {
				switch(n->getOpcode()) {
					case 0: // PtrMemD  // 
					case 1: // PtrMemI
						{
							n1 = resultstack.top();
							resultstack.pop();
							n2 = resultstack.top();
							resultstack.pop();
							if(n1->getType()==RVALUE || n2->getType()==RVALUE){
								printf("Lvalue expected\n");
								return false;
							}else if(n2->getLvalue()->getRvalue()!=NULL){
								printf("id expected\n");
								return false;
							}

							rv = new Rvalue();

							rv->appendValue("+", " ");
							if(n1->getLvalue()->getRvalue()!=NULL){
								rv->appendValue(n1->getLvalue()->getRvalue()->getValue(), " ");
								rv->setList(n1->getLvalue()->getRvalue()->getList());
							} else{
								rv->appendValue(n1->getLvalue()->getId(), " ");
							}
							rv->appendValue("(offset ", n2->getLvalue()->getId());
							rv->appendValue(")", "");

							n1->getLvalue()->setRvalue(rv);

							break;
						}             
					case 2: // Mul
					case 3: // Div
					case 4: // Rem
					case 5: // Add
					case 6: // Sub
					case 7: // Shl
					case 8: // Shr
					case 9: // LT
					case 10: // GT
					case 11: // LE
					case 12: // GE
					case 13: // EQ
					case 14: // NE
					case 15: // And
					case 16: // Xor
					case 17: // Or
						{
							n1 = resultstack.top();
							resultstack.pop();
							n2 = resultstack.top();
							resultstack.pop();

							if (n1 == NULL || n2 == NULL) printf("NOT ENOUGH OPERANDS FOR BINOP");

							if (n1->getType() == LVALUE){
								rv = lvToRv(n, n1->getLvalue());
								n1 = new Node();
								n1->setKind(3);
								n1->setType(RVALUE);
								n1->setRvalue(rv);
							}

							if (n2->getType() == LVALUE){							
								lv = n2->getLvalue();
								rv = lvToRv(n, lv);
								n2 = new Node();
								n2->setKind(3);
								n2->setType(RVALUE);
								n2->setRvalue(rv);
							}
							rv = new Rvalue();
							// need to implement binJoin function
							char tmpList[256][256];
							
							int i=0;														
							while(strcmp(n2->getRvalue()->rv_e[i], EOL)!=0){
								strcpy(tmpList[i], n2->getRvalue()->rv_e[i]);
								i++;
							}
							strcpy(tmpList[i], EOL);
							switch(n->getOpcode()){
								case 2: // Mul									
									binJoin("*", tmpList, n1->getRvalue()->rv_e);
									break;
								case 3: // Div
									binJoin("/", tmpList, n1->getRvalue()->rv_e);
									break;
								case 4: // Rem
									binJoin("%", tmpList, n1->getRvalue()->rv_e);
									break;
								case 5: // Add
									//rv->appendValue("(+ ",n1->getRvalue()->getValue());
									binJoin("+", tmpList, n1->getRvalue()->rv_e);
									break;
								case 6: // Sub
									binJoin("-", tmpList, n1->getRvalue()->rv_e);
									break;
								case 7: // Shl
									binJoin("+", tmpList, n1->getRvalue()->rv_e);
									break;
								case 8: // Shr
									binJoin("+", tmpList, n1->getRvalue()->rv_e);
									break;
								case 9: // LT
									binJoin("<", tmpList, n1->getRvalue()->rv_e);
									break;
								case 10: // GT
									binJoin(">", tmpList, n1->getRvalue()->rv_e);
									break;
								case 11: // LE
									binJoin("<=", tmpList, n1->getRvalue()->rv_e);
									break;
								case 12: // GE
									binJoin(">=", tmpList, n1->getRvalue()->rv_e);
									break;
								case 13: // EQ
									binJoin("==", tmpList, n1->getRvalue()->rv_e);
									break;
								case 14: // NE
									binJoin("!=", tmpList, n1->getRvalue()->rv_e);
									break;
								case 15: // And
									binJoin("&&", tmpList, n1->getRvalue()->rv_e);
									break;
								case 16: // Xor
									binJoin("+", tmpList, n1->getRvalue()->rv_e);
									break;
								case 17: // Or
									binJoin("||", tmpList, n1->getRvalue()->rv_e);
									break;
							}					
							//rv->setValue(strcat(rv->getValue(), " "));
							//rv->setValue(strcat(rv->getValue(), n2->getRvalue()->getValue()));
							//rv->setValue(strcat(rv->getValue(), ")"));
							i=0;
							while(strcmp(tmpList[i], EOL)!=0){
								strcpy(rv->rv_e[i], tmpList[i]);
								i++;
							}
							strcpy(rv->rv_e[i], EOL);

							list<evt*>* mo = merge_unordered(n1->getRvalue()->getList(), n2->getRvalue()->getList());

							list<evt*>::iterator it = mo->begin();
							it = mo->begin();
							if(it != mo->end()) {
								if((*it)->getState() == EVT_STATE_UNDEF) {
									emitWarning(n->getSLoc(), "MSP");
								}
							}

							rv->setList(mo);

							n = new Node();
							n->setType(RVALUE);
							n->setKind(3);						
							n->setRvalue(rv);
							//cout << "hjg " << n->getRvalue()->getList() << endl;
							resultstack.push(n);
							break;
						}
					case 18: // Land
					case 19: // LOr
						n1 = resultstack.top();
						resultstack.pop();
						n2 = resultstack.top();
						resultstack.pop();

						if (n1 == NULL || n2 == NULL) printf("NOT ENOUGH OPERANDS FOR LOGICAL OPERATOR");

						if (n1->getType() == LVALUE){
							rv = lvToRv(n, n1->getLvalue());
							n1 = new Node();
							n1->setKind(3);
							n1->setType(RVALUE);
							n1->setRvalue(rv);
						}

						if (n2->getType() == LVALUE){							
							rv = lvToRv(n, n1->getLvalue());
							n2 = new Node();
							n2->setKind(3);
							n2->setType(RVALUE);
							n2->setRvalue(rv);
						}
						rv = new Rvalue();
						// need to implement binJoin function
						//rv->setValueList(0, RVE_OR);
						//rv->setValueList(1, "0");
						//rv->setValueList(2, "1");
						//rv->setValueList(3, EOL);
						rv->setValue("OR 0 1");
						rv->setList(merge_seq(n1->getRvalue()->getList(), n2->getRvalue()->getList()));

						n = new Node();
						n->setType(RVALUE);
						n->setKind(3);						
						n->setRvalue(rv);
						resultstack.push(n);
						break;

					case 20: // ASSIGN
						{
							n1 = resultstack.top();   //pointer to top of stack
							resultstack.pop();	//pop from stack
							n2 = resultstack.top();	// new pointer to top of new stack 
							resultstack.pop();	//Another pop

							if(n1->getKind()==RVALUE){
								printf("Lvalue required\n");
								break;
							}						

							if(n2->getType()==LVALUE){
								// llvalue to rvalue conversion
								n2->setRvalue(lvToRv(n, n2->getLvalue())); 
								n2->setLvalue(NULL);
								n2->setType(RVALUE);
							}
							list<evt*>* tmp_evt = new list<evt*>();
							tmp_evt->push_back(new evt(n1->getLvalue()->getId(), EVT_STATE_W));
							list<evt*>* n2list = n2->getRvalue()->getList();
							list<evt*>* n1list = n1->getLvalue()->getList();
							list<evt*>* mu = merge_unordered(n2list, n1list);
							list<evt*>* mo = merge_ordered(mu,tmp_evt);

							list<evt*>::iterator it = mo->begin();
							it = mo->begin();
							if(it != mo->end()) {
								if((*it)->getState() == EVT_STATE_UNDEF) {
									emitWarning(n->getSLoc(), "MSP");
								}
							}

							n2->getRvalue()->setList(mo);

							resultstack.push(n2);
							break;
						}
					case 31: // Comma
						{
							n1 = resultstack.top();
							resultstack.pop();
							n2 = resultstack.top();
							resultstack.pop();

							if (n1 == NULL || n2 == NULL) printf("NOT ENOUGH OPERANDS FOR LOGICAL OP");

							if (n1->getType() == LVALUE){
								rv = lvToRv(n, n1->getLvalue());
								n1 = new Node();
								n1->setKind(3);
								n1->setType(RVALUE);
								n1->setRvalue(rv);
							}

							if (n2->getType() == LVALUE){							
								rv = lvToRv(n, n2->getLvalue());
								n2 = new Node();
								n2->setKind(3);
								n2->setType(RVALUE);
								n2->setRvalue(rv);
							}

							rv = new Rvalue();
							// need to implement binJoin function
							rv->setValue(n2->getRvalue()->getValue());
							list<evt*>* tmpList = new list<evt*>();
							for (list<evt*>::iterator it = n1->getRvalue()->getList()->begin();
									it != n1->getRvalue()->getList()->end();
									it++) {
								tmpList->push_back(new evt((*it)->getId(), EVT_STATE_SW));
							}

							rv->setList(merge_seq(tmpList, n2->getRvalue()->getList()));

							n = new Node();
							n->setType(RVALUE);
							n->setKind(3);						
							n->setRvalue(rv);
							resultstack.push(n);
							break;
						}
					case 21: // Compound_Mul
					case 22: // Compound_Div
					case 23: // Compound_Rem
					case 24: // Compound_Add
					case 25: // Compound_Sub
					case 26: // Compound_Shl   //shift towards left
					case 27: // Compound_Shr   //shift towards right	
						n1 = resultstack.top();
						resultstack.pop();
						n2 = resultstack.top();
						resultstack.pop();

						//cout << "LLL : " << n1 << endl;

						if (n1 == NULL || n2 == NULL) printf("NOT ENOUGH OPERANDS FOR LOGICAL OP");

						rv = new Rvalue();
						if(n1->getType() == LVALUE) {
							if ( n1->getLvalue()->getId()!=NULL || strcmp(n1->getLvalue()->getId(), "") != 0){
								rv->setValue(n1->getLvalue()->getId());
							}else{
								rv->setValue(n1->getLvalue()->getRvalue()->getValue());
							}
						}else{
							printf("INVALID NODE TYPE IN COMPOUND OP");
						}

						newNode = new Node();
						//cout << "new node : " << rv->getList() << endl;
						newNode->setKind(3);
						newNode->setType(RVALUE);
						newNode->setRvalue(rv);

						assignNode = new Node();
						assignNode->setKind(2);
						assignNode->setOpcode(20);

						opNode = new Node();
						opNode->setKind(2);
						opNode->setOpcode(n->getOpcode()-19);

						nodestack.push(assignNode);
						nodestack.push(n1);
						/*
						   cout << "compound n1 :" << n1 << endl;
						   cout << "compound n1 list: " << n1->getLvalue()->getRvalue()->getList() << endl;
						   cout << "compound n1 list: " << n1->getLvalue()->getRvalue()->getList()->size() << endl;
						 */
						nodestack.push(opNode);
						resultstack.push(newNode);
						resultstack.push(n2);
						break;

					case 28: // Compound_And
					case 29: // Compound_Or
					case 30: // Compound_Xor
						n1 = resultstack.top();
						resultstack.pop();
						n2 = resultstack.top();
						resultstack.pop();

						if (n1 == NULL || n2 == NULL) printf("NOT ENOUGH OPERANDS FOR LOGICAL OP");

						rv = new Rvalue();
						if(n1->getType() == LVALUE) {
							if ( n1->getLvalue()->getId()!=NULL || strcmp(n1->getLvalue()->getId(), "") != 0){
								rv->setValue(n1->getLvalue()->getId());
							}else{
								rv->setValue(n1->getRvalue()->getValue());
							}
						}else{
							printf("INVALID NODE TYPE IN COMPOUND OP");
						}

						newNode = new Node();
						newNode->setKind(3);
						newNode->setType(RVALUE);
						newNode->setRvalue(rv);

						Node* assignNode = new Node();
						assignNode->setKind(2);
						assignNode->setOpcode(20);

						Node* opNode = new Node();
						opNode->setKind(2);

						if (n->getOpcode() == 28)
							opNode->setOpcode(15);
						if (n->getOpcode() == 29)
							opNode->setOpcode(17);
						if (n->getOpcode() == 30)
							opNode->setOpcode(16);

						nodestack.push(assignNode);
						nodestack.push(n1);
						nodestack.push(opNode);
						resultstack.push(n2);
						resultstack.push(newNode);
						break;

				}
			} else if(n->getKind() == 4) {     //Conditional OPS
				switch(n->getOpcode()) {
					case 0:
						{	
							bool lv_rv = false;
							// c?x:y (format)
							n1 = resultstack.top();  // c
							resultstack.pop();
							n2 = resultstack.top();	 // x
							resultstack.pop();
							n3 = resultstack.top();  // y
							resultstack.pop();

							if (n1 == NULL || n2 == NULL || n3 == NULL) printf("NOT ENOUGH OPERANDS FOR Conditional Operators");

							if(n2->getType() == LVALUE && n3->getType()==LVALUE){
								if (n3->getType() == LVALUE){
									rv = lvToRv(n, n3->getLvalue());
									n3 = new Node();
									n3->setKind(3);
									n3->setType(RVALUE);
									n3->setRvalue(rv);
								}

								if (n2->getType() == LVALUE){							
									rv = lvToRv(n, n2->getLvalue());
									n2 = new Node();
									n2->setKind(3);
									n2->setType(RVALUE);
									n2->setRvalue(rv);
								}
								lv_rv = true;
							}else if(n2->getType() == RVALUE && n3->getType() == RVALUE){
								lv_rv = false;
							}else{
								printf("Type of conditional statements are different");
								break;
							}

							rv = new Rvalue();
							// need to implement binJoin function
							//rv->setValue("OR");
							int i=0;
							char tmpList[256][256];
							while(true){
								strcpy(tmpList[i], n2->getRvalue()->rv_e[i]);
								i++;
								if(strcmp(n2->getRvalue()->rv_e[i], EOL)==0) break;
							}
							strcpy(tmpList[i], EOL);

							condJoin(tmpList, n3->getRvalue()->rv_e);
							i=0;
							while(true){
								strcpy(rv->rv_e[i], tmpList[i]);
								i++;
								if(strcmp(tmpList[i], EOL)==0) break;
							}
							rv->setValueList(i, EOL);

							list<evt*>* tmp = merge_seq(n2->getRvalue()->getList(), n3->getRvalue()->getList());
							rv->setList(tmp);

							if (lv_rv){
								n = new Node();
								n->setType(LVALUE);
								n->setKind(3);						
								lv = new Lvalue();
								lv->setRvalue(rv);
								n->setLvalue(lv);				
								resultstack.push(n);
								break;
							}else{
								n = new Node();
								n->setType(RVALUE);
								n->setKind(3);
								n->setRvalue(rv);
								resultstack.push(n);
								break;
							}
						} 
					case 1:
						{
							n1 = resultstack.top();
							resultstack.pop();
							rv = new Rvalue();

							if(n1->getType()==LVALUE){
								n1->setType(RVALUE);
								n1->setRvalue(lvToRv(n1, n1->getLvalue()));
							}			

							rv->appendValue("call ", n1->getRvalue()->getValue());

							list<evt*>* tmp_evt = new list<evt*>();

							for(int i=1;i<n->getType();i++){
								n2 = resultstack.top();
								resultstack.pop();
								if(n2->getType() == LVALUE)
									n2->setRvalue(lvToRv(n2, n2->getLvalue())); 
								rv->appendValue(" ", n2->getRvalue()->getValue());
								tmp_evt = merge_unordered(tmp_evt, WtoSW(n2->getRvalue()->getList()));
							}
							//printf("%s\n", rv->rv_e[0]); //CODING
							n1->setRvalue(rv);
							n1->getRvalue()->setList(merge_unordered(n1->getRvalue()->getList(), tmp_evt));
							resultstack.push(n1);
							break;	
						}             
				}
			} else {
				resultstack.push(n);
			}

			//printf("%u %u %d %s\n", n->getKind(), n->getOpcode(), n->getType(), 
			//(n->getKind()==3)?(n->getType()==1)?(n->getLvalue())->getId():(n->getRvalue())->getValue() : "");
			/*
			rv = NULL;
			n = resultstack.top();
			if (n->getKind() == 3 && n->getType()==RVALUE){
				rv = n->getRvalue();
			} else if(n->getKind()==3 && n->getType()==LVALUE && n->getLvalue()->getRvalue()!=NULL){
				rv = n->getLvalue()->getRvalue();
			}
			if(rv!=NULL){
				int i=0;
				while(strcmp(rv->rv_e[i], EOL)!=0){
					printf("\t%s\n", rv->rv_e[i]);
					i++;
				}
					
				list<evt*>::iterator it1 = rv->getList()->begin();
				while(it1 != rv->getList()->end()){					
					printf("\t\t%s %d\n",(*it1)->getId(), (*it1)->getState());
					it1++;
				}
			}
			*/
			
		}
		
		//printf("out of while\n");
		//printf("\n");
	}                                                                     
	return true;                                                          
}


/*
   bool TraverseBinMul(BinaryOperator* B) {
   TraverseStmt(B->getLHS()); // LHS becomes rvalue
   TraverseStmt(B->getRHS()); // RHS becomes rvalue
   WalkUpFromBinMul(B);
   return true;
   }

   bool TraverseImplicitCastExpr(ImplicitCastExpr *E) {
   for (Stmt::child_iterator C = E->child_begin(), 
   CEnd = E->child_end();
   C != CEnd; ++C) {
   TraverseStmt(*C);
   }    
   WalkUpFromImplicitCastExpr(E);
   return true;
   }

   bool VisitDeclRefExpr(DeclRefExpr *E){
   std::string kind = E->isRValue() ? "(R)" : "(L)";
   std::string e = E->getNameInfo().getName().getAsString();
   llvm::errs() <<"DeclRef: "<< e  <<kind<<"\n";
   return true;
   }
 */

bool VisitImplicitCastExpr(ImplicitCastExpr *E){
	if (E->getCastKind() == CK_LValueToRValue) {
		//emitWarning(E->getLocStart(), "Missing Sequence Point error");
	}
	return true;
}

/*
// guarantees operands are all evaluated
bool VisitBinMul(BinaryOperator* B) {
llvm::errs() <<"visited *\n";
Stmt *S = cast<Stmt>(B);
//S->dumpAll();
return true;
}
 */
 
bool VisitCallExpr(CallExpr *S){
	int a=0;
	for(Stmt::child_range range = S->children(); range; ++range)
		a++;
	Node *n = new Node();
	Rvalue *rv = new Rvalue();
	rv->setValue("\\constant\\");
	n->setKind(4);
	n->setOpcode(1);
	n->setRvalue(rv);
	n->setType(a);
	n->setSLoc(S->getLocStart());
	nodestack.push(n);
	return true;
}
 
bool VisitBinaryConditionalOperator(BinaryConditionalOperator *S) {
	//printf("1\n");
	return true;
}

bool VisitConditionalOperator(ConditionalOperator *S) {
	Node *n = new Node();
	n->setKind(4);
	n->setOpcode(0);
	n->setSLoc(S->getLocStart());
	nodestack.push(n);
	return true;
}

bool VisitIntegerLiteral(IntegerLiteral *S){
	Node *n = new Node();
	Rvalue *rv = new Rvalue();
	rv->setValue("\\constant\\");
	n->setKind(3);
	n->setOpcode(1);
	n->setRvalue(rv);
	n->setType(2);
	nodestack.push(n);
	return true;
}

bool VisitCharacterLiteral(CharacterLiteral *S){
	Node *n = new Node();
	Rvalue *rv = new Rvalue();
	rv->setValue("\\constant\\");
	n->setKind(3);
	n->setOpcode(2);
	n->setRvalue(rv);
	n->setType(2);
	nodestack.push(n);
	return true;
}

bool VisitFloatingLiteral(FloatingLiteral *S){
	Node *n = new Node();
	Rvalue *rv = new Rvalue();
	rv->setValue("\\constant\\");
	n->setKind(3);
	n->setOpcode(3);
	n->setRvalue(rv);
	n->setType(2);
	nodestack.push(n);
	return true;
}

bool VisitImaginaryLiteral(ImaginaryLiteral *S){
	Node *n = new Node();
	Rvalue *rv = new Rvalue();
	rv->setValue("\\constant\\");
	n->setKind(3);
	n->setOpcode(4);
	n->setRvalue(rv);
	n->setType(2);
	nodestack.push(n);
	return true;
}

bool VisitStringLiteral(StringLiteral *S){
	Node *n = new Node();
	Rvalue *rv = new Rvalue();
	rv->setValue("\\constant\\");
	n->setKind(3);
	n->setOpcode(5);
	n->setRvalue(rv);
	n->setType(2);
	nodestack.push(n);
	return true;
}

bool VisitObjCStringLiteral(ObjCStringLiteral *S){
	Node *n = new Node();
	Rvalue *rv = new Rvalue();
	rv->setValue("\\constant\\");
	n->setKind(3);
	n->setOpcode(6);
	n->setRvalue(rv);
	n->setType(2);
	nodestack.push(n);
	return true;
}

void HandleTranslationUnit(ASTContext &Ctx) {
	fprintf(stderr, "Welcome to MSP detector!\n");

	TraverseDecl(Ctx.getTranslationUnitDecl());

	/*
	   Node* n;
	   Lvalue* lv;
	   while(!nodestack.empty()) {
	   n = nodestack.top();
	   nodestack.pop();
	   lv = n->getLvalue();
	//printf("%u %u %s %d\n", n->getKind(), n->getOpcode(), lv->getId(), n->getType());
	}
	//printf("\n");
	 */
}

}; 


class DetectMspAction : public PluginASTAction {
	protected:
		ASTConsumer *CreateASTConsumer(CompilerInstance &CI, llvm::StringRef) {
			return new DetectMspConsumer(CI);
		}
		bool ParseArgs(const CompilerInstance &CI,
				const std::vector<std::string>& args) {
			for (unsigned i = 0, e = args.size(); i != e; ++i) {
				llvm::errs() << "MspDetector arg = " << args[i] << "\n";


				// Example error handling.
				if (args[i] == "-an-error") {
					Diagnostic &D = CI.getDiagnostics();
					unsigned DiagID = D.getCustomDiagID(
							Diagnostic::Error, "invalid argument '" + args[i] + "'");
					D.Report(DiagID);
					return false;
				}
			}
			if (args.size() && args[0] == "help")
				PrintHelp(llvm::errs());


			return true;
		}
		void PrintHelp(llvm::raw_ostream& ros) {
			ros << "Help for DetectMsp plugin goes here\n";
		}
};
}


static FrontendPluginRegistry::Add<DetectMspAction>
X("detect-msp", "detect missing sequence points");
