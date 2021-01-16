//===- PtsToEnum.cpp - Enumerating all poitner accesses  --------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// A working prototype that converts pointer accesses to enumerated loads and 
// stores.  
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/TypeBuilder.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/ConstantFolder.h"
#include "llvm/IR/Operator.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/FunctionComparator.h"
#include "llvm/IR/SymbolTableListTraits.h"
#include "llvm/Analysis/DependenceAnalysis.h"
#include <map>
#include <vector>
#include <stack>
#include <algorithm>
#include <iostream>
#include <sstream>
#include <fstream>
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FormattedStream.h"


using namespace llvm;
using namespace std;

struct PtsToEnum : public ModulePass {
  static char ID;
  Module *mod; 

  /// The type for the list of global variables.
  using GlobalListType = SymbolTableList<GlobalVariable>;
  GlobalListType *gList;
  PtsToEnum() : ModulePass(ID)
  {
  }
  bool runOnModule(Module &M) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }
};

std::error_code EC;
raw_fd_ostream logFile("ptsToEnum.log", EC, llvm::sys::fs::F_None);
char PtsToEnum::ID = 0;
static RegisterPass<PtsToEnum> X("ptsTo", "Handling pointer accesses",
    false /* Only looks at CFG */,
    true /* Transformation Pass */);

std::vector<Value*> globalVarMap;
std::map<Value*,Value*> indexMap;
std::map<Instruction*,std::vector<Value*>> ptsToGraph; 
std::map<Argument*,std::vector<Value*>> argsPtsToGraph; 

int getIndex(Value *val){
  llvm::formatted_raw_ostream log(logFile);
  int index = 0;
  std::vector<Value*>::iterator gv = std::find(globalVarMap.begin(),globalVarMap.end(),val);
  if(gv!=globalVarMap.end()) {
    log << "GV: " << **gv << "\n";
    index = std::distance(globalVarMap.begin(), gv) + 1;
    log << "Index: " << index << "\n";
  }
  return index;
}

bool isDoublePtr(Value *V) {
  return V->getType()->isPointerTy() && V->getType()->getContainedType(0)->isPointerTy();
}

string getString(Value *V){
  std::string tmp;
  raw_string_ostream Out(tmp);
  V->printAsOperand(Out, false);
  return tmp;
}

int strToInt(std::string str) {
  int out;
  std::stringstream convert(str);
  assert(convert >> out);
  return out;
}

int ptsCount = 0;
int instCount = 0;

void getExternalPtsToForArgs(Argument *I) {
  llvm::formatted_raw_ostream log(logFile);
  assert(isa<Argument>(I));
  log << "Argument is " << *I << "\n";
  std::ifstream infile("pointsTo.Vitis");
  bool found = false;
  if (infile.is_open()) {
    string line;
    while(getline(infile,line)){
      if(found) break;
      stringstream linestream(line);
      string val;
      // Read first column
      getline(linestream,val,':');
      // Check if it is the right function for SSA reasons
      if(val == I->getParent()->getName()){
        log << "Found function " << val << "\n";
        // Read first column
        getline(linestream,val,':');
        //Handling Load Instruction
        if(val =="aargument"){
          //log << "Found Store inst\n";
          // Get Instruction label and address operand
          string argLabel = getString(I);
          string argLabelComp = argLabel;
          //log << "argLabel: " << argLabelComp << "\n";

          // Check if operand points to a global variable or Alloc 

          // Read the next three columns
          string op0,countstr;
          getline(linestream,op0,':');
          getline(linestream,countstr,':');
          int count = strToInt(countstr);

          // Check if the Instruction and input aa line is a match
          if(op0==argLabelComp){
            log << "Found a match!\n";
            if(count>0){
              string globalName;
              std::vector<Value*> ptsToSet;
              while(getline(linestream, globalName, ':')){
                //log << "Global name is " << globalName << "\n";
                for(vector<Value*>::iterator gvar = globalVarMap.begin(); gvar != globalVarMap.end(); gvar++){
                  Value *g = *gvar;
                  string name = getString(g);
                  if(name==globalName) {
                    log << "Found inst: " << *g << "\n";
                    ptsToSet.push_back(*gvar);
                  }
                }
              }
              argsPtsToGraph[&(*I)] = ptsToSet;
            }
          }
        }
      }
    }
  }
  infile.close();
  log << "Finished\n";
}


void getExternalPtsTo(Module *mod){
  llvm::formatted_raw_ostream log(logFile);

  // Extracting external point 
  for(Module::iterator F = mod->begin(); F != mod->end(); F++){
    for(Function::iterator BB = F->begin(); BB != F->end(); BB++){
      for(BasicBlock::iterator I = BB->begin(); I != BB->end(); I++){
        if(isa<StoreInst>(I)||isa<LoadInst>(I)||isa<GetElementPtrInst>(I)){
          log << "Function is " << F->getName() << "\n";
          log << "Instruction is " << *I << "\n";
          std::ifstream infile("pointsTo.Vitis");
          bool found = false;
          std::vector<Value*> inPtsToSet = ptsToGraph[&(*I)];
          log << "Size is " << inPtsToSet.size() << "\n";
          if(inPtsToSet.size()>0) continue;

          if (infile.is_open()) {
            string line;
            while(getline(infile,line)){
              if(found) break;
              stringstream linestream(line);
              string val;
              // Read first column
              getline(linestream,val,':');
              // Check if it is the right function for SSA reasons
              if(val == I->getParent()->getParent()->getName()){
                // Read first column
                getline(linestream,val,':');
                //Handling Load Instruction
                if(LoadInst *V = dyn_cast<LoadInst>(I)){
                  if(val =="load"){
                    // Get Instruction label and address operand
                    string labelName = getString(V);
                    string addrLabel = getString(V->getOperand(0));
                    string addrLabelComp = addrLabel;
                    string op0,op1,countstr;
                    getline(linestream,op0,':');
                    getline(linestream,op1,':');
                    getline(linestream,countstr,':');
                    int count = strToInt(countstr);

                    // Check if the Instruction and input aa line is a match
                    if(op0==labelName && op1==addrLabelComp){
                      log << "Found a match!\n";
                      found = true;
                      if(count>0){
                        string globalName;
                        std::vector<Value*> ptsToSet;
                        while(getline(linestream, globalName, ':')){
                          for(vector<Value*>::iterator gvar = globalVarMap.begin(); gvar != globalVarMap.end(); gvar++){
                            Value *g = *gvar;
                            string name = getString(g);
                            if(name==globalName) {
                              log << "Found inst: " << name << "\n";
                              ptsToSet.push_back(*gvar);
                            }
                          }
                        }
                        ptsToGraph[&(*I)] = ptsToSet;
                      }
                    }
                  }
                }
                else if(StoreInst *V = dyn_cast<StoreInst>(I)){
                  if(val =="store"){
                    // Get Instruction label and address operand
                    string writeLabel = getString(V->getOperand(0));
                    string addrLabel =  getString(V->getOperand(1));
                    string writeLabelComp = writeLabel;
                    string addrLabelComp = addrLabel;
                    // Read the next three columns
                    string op0,op1,countstr;
                    getline(linestream,op0,':');
                    getline(linestream,op1,':');
                    getline(linestream,countstr,':');
                    int count = strToInt(countstr);

                    // Check if the Instruction and input aa line is a match
                    if(op0==writeLabelComp && op1==addrLabelComp){
                      log << "Found a match!\n";
                      found = true;
                      if(count>0){
                        string globalName;
                        std::vector<Value*> ptsToSet;
                        while(getline(linestream, globalName, ':')){
                          //log << "Global name is " << globalName << "\n";
                          for(vector<Value*>::iterator gvar = globalVarMap.begin(); gvar != globalVarMap.end(); gvar++){
                            Value *g = *gvar;
                            string name = getString(g);
                            if(name==globalName) {
                              log << "Found inst: " << *g << "\n";
                              ptsToSet.push_back(*gvar);
                            }
                          }
                        }
                        ptsToGraph[&(*I)] = ptsToSet;
                      }
                    }
                  }
                }
                else if(GetElementPtrInst *V = dyn_cast<GetElementPtrInst>(I)){
                  if(val =="agep"){
                    // Get Instruction label and address operand
                    string opLabel0 = getString(V->getOperand(0));
                    string writeLabel = getString(V);
                    // Read the next three columns
                    string write,op0,countstr;
                    getline(linestream,write,':');
                    getline(linestream,op0,':');
                    getline(linestream,countstr,':');
                    int count = strToInt(countstr);
                    // Check if the Instruction and input aa line is a match
                    if(write==writeLabel){
                      log << "Found a match!\n";
                      found = true;
                      // Check count of whether AA gives us any info
                      if(count>0){
                        string globalName;
                        std::vector<Value*> ptsToSet;
                        while(getline(linestream, globalName, ':')){
                          //log << "Global name is " << globalName << "\n";
                          for(vector<Value*>::iterator gvar = globalVarMap.begin(); gvar != globalVarMap.end(); gvar++){
                            Value *g = *gvar;
                            string name = getString(g);
                            if(name==globalName) {
                              log << "Found inst: " << *g << "\n";
                              ptsToSet.push_back(*gvar);
                            }
                          }
                        }
                        ptsToGraph[&(*I)] = ptsToSet;
                      }
                    }
                  }
                }
              }
            }
          }
          infile.close();
        }
      }
    }
  }
}

void printPtsTo(){
  llvm::formatted_raw_ostream log(logFile);
  // DEBUG: Print out points-to graph 
  for(std::map<Instruction*,std::vector<Value*>>::iterator i = ptsToGraph.begin(); i != ptsToGraph.end(); i++){
    log << "Instruction " << *i->first << " points to :\n";
    std::vector<Value*> ptsToSet;
    ptsToSet = i->second;
    for(std::vector<Value*>::iterator j = ptsToSet.begin(); j!= ptsToSet.end(); j++){
      log << "Value " << **j << "\n";
    }
  }
}

bool PtsToEnum::runOnModule(Module &M) {
  LLVMContext &c = M.getContext();
  mod = &M;
  gList = &mod->getGlobalList();
  llvm::formatted_raw_ostream log(logFile);

  // Creating indices for globals 
  for (auto GV = gList->begin(); GV != gList->end(); GV++){
    // Getting globals that are pointers 
    //if(GV->getType()->isPointerTy()){
      if(
          // Avoiding all llvm metadata or strings 
          GV->getLinkage()!=GlobalValue::PrivateLinkage && 
          GV->getLinkage()!=GlobalValue::AppendingLinkage
          // and not considering arrays either for now! 
          //!GV->getType()->getContainedType(0)->isAggregateType()
        ){
        globalVarMap.push_back(&(*GV));
        log << "Pushing " << *GV << "\n";
      }
    //}
  }
  // Identifies all global variables that are double pointers  
  // For each identified variable, we create another variable that is not a pointer to hold the index
  for (auto GV = gList->begin(); GV != gList->end(); GV++){
    //int index = getIndex(&(*GV));
    if(
        isDoublePtr(&(*GV))
        //|| GV->getType()->getContainedType(0)->isAggregateType()
      ){
      log << "Double pointer spotted: " << *GV << "\n";
      Value *indexedGVal = M.getOrInsertGlobal(GV->getName().str() + "_index", TypeBuilder<int,false>::get(c));
      GlobalVariable *indexedGVar = dyn_cast<GlobalVariable>(indexedGVal);       
      indexedGVar->setInitializer(ConstantInt::get(c, APInt(32,0)));
      log << "Creating global variable " << *indexedGVar; 
      indexMap[&(*GV)] = indexedGVar;
      log << "\n";
    }
  }
  log << "size of indexMap is " << indexMap.size() << "\n";

  int retVal = system("if [ -f config ]; then exit 1; else exit 0; fi");
  log << "Return value was " << retVal << "\n";

  if(!retVal){
    log << "No config!\n";
    // Find all loads and stores and assign points to all global variables 
    // This is the most conservative approach 

    for(Module::iterator F = mod->begin(); F != mod->end(); F++){
      for(Function::iterator BB = F->begin(); BB != F->end(); BB++){
        for(BasicBlock::iterator I = BB->begin(); I != BB->end(); I++){
          if(isa<StoreInst>(I)||isa<LoadInst>(I)||isa<GetElementPtrInst>(I)){
            std::vector<Value*> ptsToSet;
            ptsToSet = globalVarMap;
            ptsToGraph[&(*I)] = ptsToSet;
          }
        }
      }
    }
  }
  else
  {
    log << "Found config!\n";
    system("./script.sh");

    getExternalPtsTo(mod);
  }

  printPtsTo();



  std::map<Value*,Value*> replaceMap;
  std::vector<Instruction*> removalList;
  Type *intTy = TypeBuilder<int,false>::get(c);

  // Handle direct loads and stores to double pointers! 
  for(Module::iterator F = mod->begin(); F != mod->end(); F++){
    for(Function::iterator BB = F->begin(); BB != F->end(); BB++){
      for (Function::arg_iterator arg = F->arg_begin(); arg != F->arg_end(); arg++) {
        getExternalPtsToForArgs(&(*arg));
      }
      for(BasicBlock::iterator I = BB->begin(); I != BB->end(); I++){
        // Setting insertion point.
        IRBuilder<> builder(I->getParent());
        builder.SetInsertPoint(&(*I));

        // Load instructions
        log << "Instr: " << *I << "\n";
        if(LoadInst *lInst = dyn_cast<LoadInst>(I)){
          log << "Found load: " << *lInst << "\n";
          // if address is in indexmap, then it is a direct access to a global 
          std::map<Value*,Value*>::iterator it = indexMap.find(lInst->getPointerOperand());
          if (it != indexMap.end()) {
            instCount++;
            // Simply replace the pointer-based load with a integer-based load
            Value *oldLoad = it->second; 
            Value *newLoad = builder.CreateLoad(oldLoad, true, oldLoad->getName().str() + "_load");
            log << "Direct load:" << *newLoad << "\n";

            // House-keeping for replacing and removing redundant loads 
            replaceMap.insert(std::pair<Value*, Value*>(lInst,newLoad));
            removalList.push_back(lInst);
            ptsCount++;
          } else {
            if(LoadInst *load = dyn_cast<LoadInst>(lInst->getPointerOperand())){
              log << "Found indirect load: " << *load << "\n";
              // All indirect addresses are in the replacement map 
              Value *addrCompLoad;
              std::map<Value*,Value*>::iterator base = replaceMap.find(load);
              if (base != replaceMap.end()) {
                // Get the replacement load 
                log << "Replacement load: " << *base->second << "\n";
                addrCompLoad = base->second;
              }

              // Get points-to set for the load instruction 
              // This set can be the entire set of globals or an external input.  

              std::vector<Value*> ptsToSet = ptsToGraph[load];
              Value *prevLoad, *currLoad, *currCmp, *currSelect; 
              log << "ptsTo size: " << ptsToSet.size() << "\n";
              instCount++;

              int iteration = 0;
              for(std::vector<Value*>::iterator j = ptsToSet.begin(); j!= ptsToSet.end(); j++){
                // Get address of points-to element, including if it is a pointer
                // If it is a pointer, the element is in the indexMap
                std::map<Value*,Value*>::iterator addrIt = indexMap.find(*j);
                Value *addr; 
                if (addrIt != indexMap.end()) addr = addrIt->second;
                else addr = *j;

                if(addr->getType()->getContainedType(0)->isAggregateType()) continue;

                log << "Value " << *addr << "\n";

                // Skip if the two variables are the same!
                if(LoadInst *ld = dyn_cast<LoadInst>(addrCompLoad))
                  if(ld->getPointerOperand()==addr) continue;

                ptsCount++;
                // Get relative distance of current element in points-to set
                //int dist = std::distance(ptsToSet.begin(),
                //    std::find(ptsToSet.begin(), ptsToSet.end(), &(**j)));

                if(iteration==0){
                  // Create the first load in the points-to set
                  prevLoad = builder.CreateLoad(addr, true, addr->getName().str() + "_load");
                  log << "currLoad " << *prevLoad << "\n";
                  //break;
                  iteration++;
                  continue;
                }
                iteration++;

                // For all points-to elements, create a load, get current index,
                // compare the index and finally add select statement
                currLoad = builder.CreateLoad(addr, true, addr->getName().str() + "_load");
                Constant *index = ConstantInt::get(intTy, getIndex(*j), true);
                Value *idxVal = dyn_cast<Value>(index);
                currCmp = builder.CreateICmpEQ(idxVal, addrCompLoad, 
                    addr->getName().str() + "_cmp");
                currSelect = builder.CreateSelect(currCmp,currLoad, prevLoad,
                    addr->getName().str() + "_select");
                prevLoad = currSelect;

                log << "prevLoad" << *prevLoad << "\n";
                log << "currLoad" << *currLoad << "\n";
                log << "currCmp" << *currCmp << "\n";
                log << "currSelect" << *currSelect << "\n";
              }

              // House-keeping replacing and removing loads 
              if(ptsToSet.size()>0){
                log << "Pushed replacement map\n";
                log << *lInst << " to " << *prevLoad << "\n";
                replaceMap.insert(std::pair<Value*, Value*>(lInst,prevLoad));
                removalList.push_back(lInst);
              }
            }
            else if(GetElementPtrInst *gepInst = dyn_cast<GetElementPtrInst>(lInst->getPointerOperand())){
              log << "Found an indirect GEP: " << *gepInst << "\n";
              Instruction *pts = dyn_cast<Instruction>(gepInst);
              std::vector<Value*> ptsToSet = ptsToGraph[pts];
              log << "that points to " << ptsToSet.size() << " object(s)\n";
              if(gepInst->getNumIndices()>1) continue;
              for(auto ind_begin = gepInst->idx_begin(); ind_begin != gepInst->idx_end(); ind_begin++){
                log << "gepVec: " << **ind_begin << "\n";
              }

              Value* addrCompGep = gepInst->getPointerOperand();
              std::map<Value*,Value*>::iterator base = replaceMap.find(gepInst->getPointerOperand());
              if (base != replaceMap.end()) {
                // Get the replacement store
                log << "Replacement load: " << *base->second << "\n";
                addrCompGep = base->second;
              }

              Value *repInst;
              instCount++;

              int iteration = 0;

              for(std::vector<Value*>::iterator j = ptsToSet.begin(); j!= ptsToSet.end(); j++){
                // Get address of points-to element, including if it is a pointer
                // If it is a pointer, the element is in the indexMap
                //std::map<Value*,Value*>::iterator addrIt = indexMap.find(*j);
                Value *addr; 
                //if (addrIt != indexMap.end()) addr = addrIt->second;
                //else 
                addr = *j;

                log << "Value " << *addr << "\n";
                if(!addr->getType()->getContainedType(0)->isAggregateType()) continue;
                log << "Proceeding!\n";
                ptsCount++;

                Type *intTy2 = TypeBuilder<int64_t,false>::get(c);
                Constant *zero32 = ConstantInt::get(intTy, 0, true);
                Constant *zero64 = ConstantInt::get(intTy2, 0, true);
                vector<Value*> gepVec;

                log << "Num of indices " << gepInst->getNumIndices() << "\n";
                for(auto ind_begin = gepInst->idx_begin(); ind_begin != gepInst->idx_end(); ind_begin++){
                  if(Instruction *indInst = dyn_cast<Instruction>(*ind_begin)){
                    log << "Found indice that is an instruction: " << **ind_begin << "\n";
                    gepVec.push_back(zero32);
                  }else
                    gepVec.push_back(zero64);
                }

                for(auto ind_begin = gepInst->idx_begin(); ind_begin != gepInst->idx_end(); ind_begin++){
                  gepVec.push_back(*ind_begin);
                }

                ArrayRef<Value*> gepAR(gepVec);

                log << "Addr is " << *addr << "\n";
                Value *newGep;
                newGep = builder.CreateInBoundsGEP(addr, gepAR, gepInst->getName().str() + addr->getName().str() + "_gep");
                //Value *newGep = builder.CreateInBoundsGEP(addr, gepAR, addr->getName().str() + "_gep");
                log << "New GEP generated!\n";
                log << *newGep << "\n";
                Value * currLoad = builder.CreateLoad(newGep, true, gepInst->getName().str() + addr->getName().str() + "_load");
                log << "CurrLoad: " << *currLoad << "\n";
                // Get relative distance of current element in points-to set
                //int dist = std::distance(ptsToSet.begin(),
                //    std::find(ptsToSet.begin(), ptsToSet.end(), &(**j)));

                if(iteration==0){
                  repInst = currLoad; 
                  iteration++;
                  continue;
                }
                  iteration++;

                Constant *index = ConstantInt::get(intTy, getIndex(addr), true);
                Value *idxVal = dyn_cast<Value>(index);
                Value *currCmp    = builder.CreateICmpEQ(addrCompGep, idxVal, gepInst->getName().str() +
                    addr->getName().str() + "_cmp");
                log << "CurrCmp: " << *currCmp << "\n";
                Value *currSelect = builder.CreateSelect(currCmp, currLoad, repInst, gepInst->getName().str() + 
                    addr->getName().str() + "_select");
                repInst = currSelect;
                log << "CurrSelect: " << *currSelect << "\n";
              }
              if(ptsToSet.size()>0){
                log << "Replacing: \n";
                log << *lInst << " with \n";
                log << *repInst << "\n";
                replaceMap.insert(std::pair<Value*, Value*>(lInst,repInst));
                removalList.push_back(lInst);
                //removalList.push_back(gepInst);
              }
            }
            else {
              instCount++;
              ptsCount++;
            }
          }
        }

        // Store instructions 
        if(StoreInst *sInst = dyn_cast<StoreInst>(I)){
          log << "Store: " << *sInst << "\n";
          log << "operand 0: " << *sInst->getOperand(0) << "\n";
          log << "operand 1: " << *sInst->getOperand(1) << "\n";
          std::map<Value*,Value*>::iterator it = indexMap.find(sInst->getPointerOperand());
          if (it != indexMap.end()) {
            instCount++;
            int in;
            if(Argument *arg = dyn_cast<Argument>(sInst->getOperand(0))){
              log << "Argument spotted: "<< *arg <<"\n";
              in = getIndex(*argsPtsToGraph[arg].begin());
            }
            if(GEPOperator *gepOp = dyn_cast<GEPOperator>(sInst->getOperand(0)))
            {
              log << "Found GEP: " << *gepOp << "\n";
              log << "Found Address: " << *gepOp->getPointerOperand() << "\n";
              in = getIndex(gepOp->getPointerOperand());
            }else{
              in = getIndex(sInst->getOperand(0));
            }
            log << "Index is " << in << "\n";
            Constant *index = ConstantInt::get(intTy, in, true);
            Value *indexVal = dyn_cast<Value>(index);
            Value *addrVal = it->second; 
            if(in==0){
              std::map<Value*,Value*>::iterator base = replaceMap.find(sInst->getOperand(0));
              if (base != replaceMap.end()) {
                // Get the replacement store
                log << "Replacement load: " << *base->second << "\n";
                indexVal = base->second;
              }
            }
            Value *newStore = builder.CreateStore(indexVal, addrVal, true);
            log << "Injecting store " << *newStore << "\n";
            removalList.push_back(sInst);
            ptsCount++;
          }
          else{
            if(LoadInst* lInst = dyn_cast<LoadInst>(sInst->getPointerOperand())){
              log << "Found indirect load: " << *lInst << "\n";
              // All indirect addresses are in the replacement map 
              Value *addrCompLoad;
              std::map<Value*,Value*>::iterator base = replaceMap.find(lInst);
              if (base != replaceMap.end()) {
                // Get the replacement store
                log << "Replacement load: " << *base->second << "\n";
                addrCompLoad = base->second;
              }

              // Get points-to set for the load instruction 
              // This set can be the entire set of globals or an external input.  
              std::vector<Value*> ptsToSet = ptsToGraph[lInst];
              instCount++;
              log << "ptsToSet size is " << ptsToSet.size() << "\n";
              
              for(std::vector<Value*>::iterator j = ptsToSet.begin(); j!= ptsToSet.end(); j++){
                // Get address of points-to element, including if it is a pointer
                // If it is a pointer, the element is in the indexMap
                std::map<Value*,Value*>::iterator addrIt = indexMap.find(*j);
                Value *addr; 
                if (addrIt != indexMap.end()) addr = addrIt->second;
                else addr = *j;

                if(addr->getType()->getContainedType(0)->isAggregateType()) continue;
                log << "Value " << *addr << "\n";

                ptsCount++;
                // Skip if the two variables are the same!
                if(LoadInst *addrCompInst = dyn_cast<LoadInst>(addrCompLoad))
                  if(addrCompInst->getPointerOperand()==addr) continue;

                // Get index if store value itself is a pointer  
                Value *s1 = sInst->getOperand(0);
                int index = getIndex(sInst->getOperand(0));
                log << "Index is " << index << "\n";
                if(/*isDoublePtr(s1) &&*/ index>0){
                  Constant *sIndex = ConstantInt::get(intTy, getIndex(sInst->getOperand(0)), true);
                  s1 = dyn_cast<Value>(sIndex);
                }else{
                  std::map<Value*,Value*>::iterator base = replaceMap.find(sInst->getOperand(0));
                  if (base != replaceMap.end()) {
                    // Get the replacement store
                    log << "Replacement load: " << *base->second << "\n";
                    s1 = base->second;
                  }
                }

                log << "s1: " << *s1 << "\n";

                if(ptsToSet.size()==1){
                  Value *currStore  = builder.CreateStore(s1, addr, true);
                  log << "currStore" << *currStore  << "\n";
                  break;
                }else{
                  Value *currLoad = builder.CreateLoad(addr, true, sInst->getName().str() + addr->getName().str() + "_load");
                  log << "currLoad" << *currLoad << "\n";
                  Constant *index = ConstantInt::get(intTy, getIndex(*j), true);
                  Value *idxVal = dyn_cast<Value>(index);
                  Value *currCmp    = builder.CreateICmpEQ(addrCompLoad, idxVal, 
                      sInst->getName().str() + addr->getName().str() + "_cmp");
                  log << "currCmp" << *currCmp << "\n";
                  Value *currSelect = builder.CreateSelect(currCmp, s1, currLoad,
                      sInst->getName().str() + addr->getName().str() + "_select");
                  log << "currSelect" << *currSelect  << "\n";
                  Value *currStore  = builder.CreateStore(currSelect, addr, true);
                  log << "currStore" << *currStore  << "\n";
                }
              }
              if(ptsToSet.size()>0) removalList.push_back(sInst);
            } 
            else if(GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(sInst->getPointerOperand())){
              log << "Found indirect GEP: " << *gepInst << "\n";
              for(auto ind_begin = gepInst->idx_begin(); ind_begin != gepInst->idx_end(); ind_begin++){
                log << "gepVec: " << **ind_begin << "\n";
              }
              if(gepInst->getNumIndices()>1) continue;
              // All indirect addresses are in the replacement map 
              Value *addrCompLoad ; //= gepInst->getPointerOperand();
              std::map<Value*,Value*>::iterator base = replaceMap.find(gepInst->getPointerOperand());
              if (base != replaceMap.end()) {
                // Get the replacement store
                log << "Replacement load: " << *base->second << "\n";
                addrCompLoad = base->second;
              }

              // Get points-to set for the load instruction 
              // This set can be the entire set of globals or an external input.  
              std::vector<Value*> ptsToSet = ptsToGraph[gepInst];
              instCount++;
              for(std::vector<Value*>::iterator j = ptsToSet.begin(); j!= ptsToSet.end(); j++){
                // Get address of points-to element, including if it is a pointer
                // If it is a pointer, the element is in the indexMap
                Value *addr;
                addr = *j;

                log << "Value " << *addr << "\n";
                if(!addr->getType()->getContainedType(0)->isAggregateType()) continue;
                log << "Proceeding!\n";
                ptsCount++;

                Value *s1;
                std::map<Value*,Value*>::iterator base = replaceMap.find(sInst->getOperand(0));
                if (base != replaceMap.end()) {
                  // Get the replacement store
                  log << "Replacement load: " << *base->second << "\n";
                  s1 = base->second;
                } else {
                  s1 = sInst->getOperand(0);
                }

                Type *intTy2 = TypeBuilder<int64_t,false>::get(c);
                Constant *zero32 = ConstantInt::get(intTy, 0, true);
                Constant *zero64 = ConstantInt::get(intTy2, 0, true);
                vector<Value*> gepVec;

                log << "Num of indices " << gepInst->getNumIndices() << "\n";
                for(auto ind_begin = gepInst->idx_begin(); ind_begin != gepInst->idx_end(); ind_begin++){
                  if(Instruction *indInst = dyn_cast<Instruction>(*ind_begin)){
                    log << "Found indice that is an instruction: " << **ind_begin << "\n";
                    gepVec.push_back(zero32);
                  } else
                    gepVec.push_back(zero64);
                }

                for(auto ind_begin = gepInst->idx_begin(); ind_begin != gepInst->idx_end(); ind_begin++){
                  gepVec.push_back(*ind_begin);
                }

                ArrayRef<Value*> gepAR(gepVec);

                log << "Addr is " << *addr << "\n";
                Value *newGep;
                newGep = builder.CreateInBoundsGEP(addr, gepAR, gepInst->getName().str() + addr->getName().str() + "_gep");

                log << "New GEP: " << *newGep << "\n";
                log << "Value " << *addr << "\n";

                // Get index if store value itself is a pointer  
                if(ptsToSet.size()==1){
                  Value *currStore  = builder.CreateStore(sInst->getOperand(0), newGep, true);
                  log << "currStore" << *currStore  << "\n";
                  break;
                }
                Value *currLoad = builder.CreateLoad(newGep, true, gepInst->getName().str() + addr->getName().str() + "_load");
                log << "currLoad" << *currLoad << "\n";
                int ind = getIndex(addr);
                Constant *index = ConstantInt::get(intTy, ind, true);
                Value *idxVal = dyn_cast<Value>(index);
                Value *currCmp    = builder.CreateICmpEQ(addrCompLoad, idxVal, 
                    gepInst->getName().str() + addr->getName().str() + "_cmp");
                log << "currCmp" << *currCmp << "\n";
                Value *currSelect = builder.CreateSelect(currCmp, s1, currLoad,
                    gepInst->getName().str() + addr->getName().str() + "_select");
                log << "currSelect" << *currSelect << "\n";
                Value *currStore  = builder.CreateStore(currSelect, newGep, true);
                log << "currStore" << *currStore  << "\n";
              }
              if(ptsToSet.size()>0) {
                //removalList.push_back(gepInst);
                removalList.push_back(sInst);
              }
            }
            else {
              instCount++;
              ptsCount++;
            }
          }
        }
      }
    }
  }

  // replacing all loads and stores that are now redundant 
  for(std::map<Value*,Value*>::reverse_iterator map = replaceMap.rbegin(); map != replaceMap.rend(); map++){
    log << "Replacement block\n";
    log << "Use of: " << *map->first << "\n";
    log << "Repl use by: " << *map->second << "\n";
    for (auto &U : map->first->uses()) {
      User *user = U.getUser();  // A User is anything with operands.
      Instruction *u = dyn_cast<Instruction>(user);
      log << "User: " << *u << "\n";
      if(isa<GetElementPtrInst>(u)||isa<LoadInst>(u)) {
        //removalList.push_back(u);
        continue;
      }
      if(StoreInst *sInst = dyn_cast<StoreInst>(u)){
        if(U.getOperandNo()==0 && map->second!=u->getOperand(0)){
          log << "Replacing Store value: " << *u << "\n";
          user->setOperand(U.getOperandNo(), map->second);
          log << "with\n" << *user << "\n";
        }
        continue;
      }
      if(map->second==u->getOperand(U.getOperandNo()))
        continue;
      /*
      // Checkign the ICmpInst and replace operand of NULL checks... 
      if(isa<ICmpInst>(u)){
      if(isDoublePtr(u->getOperand(1))){
      Constant *compInt = ConstantInt::get(intTy, getIndex(u->getOperand(1)), true);
      Value *compVal = dyn_cast<Value>(compInt);
      user->setOperand(1, compVal);
      }
      continue;
      }
      */

      log << "Replacing User: " << *u << "\n";
      user->setOperand(U.getOperandNo(), map->second);
      log << "with\n" << *user << "\n";
    }
    std::vector<Value*> ptsToSet = ptsToGraph[dyn_cast<Instruction>(map->first)];
    log << "Size is " << ptsToSet.size() << "\n";
    if(ptsToSet.size()==1){
      // Dead code elimination
      Instruction *inst = dyn_cast<Instruction>(map->second);
      for (auto &U : map->first->uses()) {
        if(StoreInst *sInst = dyn_cast<StoreInst>(U.getUser())) continue;
        log << "Removing inst: " << *inst << "\n";
        removalList.push_back(inst);
      }
    }
  }

  // Removing instructions that are now not in use 
  for(std::vector<Instruction*>::reverse_iterator rmList = removalList.rbegin(); rmList != removalList.rend(); rmList++){
    Instruction *I = *rmList;
    log << "Removing: " << *I << "\n";
    for (auto &U : I->uses()) {
      User *user = U.getUser();  // A User is anything with operands.
      log << "User: " << *user << "\n"; 
      Instruction *rm = dyn_cast<Instruction>(user);
      /*for (auto &U1 : rm->uses()) {
        User *user1 = U1.getUser();  // A User is anything with operands.
        log << "User1: " << *user1 << "\n"; 
        Instruction *rm1 = dyn_cast<Instruction>(user1);
        (*rm1).eraseFromParent();
        }*/
      (*rm).eraseFromParent();
    }
    (*rmList)->eraseFromParent();
  }
  log << "PTSINFO! InstCount " << instCount << " PtsCount " << ptsCount << "\n";
  return true;
}
