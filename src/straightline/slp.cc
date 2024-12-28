#include "straightline/slp.h"

#include <iostream>

namespace A {
int A::CompoundStm::MaxArgs() const {
  // TODO: put your code here (lab1).
  return std::max(this->stm1->MaxArgs(), this->stm2->MaxArgs());
}

Table *A::CompoundStm::Interp(Table *t) const {
  // TODO: put your code here (lab1).
  return this->stm2->Interp( this->stm1->Interp(t) ); //从左到右依次解释执行
}

int A::AssignStm::MaxArgs() const {
  // TODO: put your code here (lab1).
  return this->exp->MaxArgs();
}

Table *A::AssignStm::Interp(Table *t) const {
  // TODO: put your code here (lab1).
  IntAndTable *intAndTable = this->exp->Interp(t); //由之前的table计算出右边表达式的值，返回值并更新表
  Table *tableToUpdate = intAndTable->t;
  int newVal = intAndTable->i;
  Table *updatedTable = tableToUpdate->Update(this->id, newVal);
  return updatedTable;
}

int A::PrintStm::MaxArgs() const {
  // TODO: put your code here (lab1).
  return this->exps->MaxArgs();
}

Table *A::PrintStm::Interp(Table *t) const {
  // TODO: put your code here (lab1).
  return this->exps->Interp(t)->t;
}

int A::IdExp::MaxArgs() const{
  return 1;
}

IntAndTable *A::IdExp::Interp(Table *t) const {
  int num = t->Lookup(this->id);
  return new IntAndTable(num,t);
}

int A::NumExp::MaxArgs() const {
  return 1;
}

IntAndTable *A::NumExp::Interp(Table *t) const {
  return new IntAndTable(this->num, t);
}

int A::OpExp::MaxArgs() const {
  return 1;
}

IntAndTable *A::OpExp::Interp(Table *t) const {
  IntAndTable *leftT = this->left->Interp(t);
  IntAndTable *rightT = this->right->Interp(leftT->t);
  switch (this->oper)
  {
  case PLUS:
    return new IntAndTable(leftT->i + rightT->i, rightT->t);
  case MINUS:
    return new IntAndTable(leftT->i - rightT->i, rightT->t);
  case TIMES:
    return new IntAndTable(leftT->i * rightT->i, rightT->t);
  case DIV:
    return new IntAndTable(leftT->i / rightT->i, rightT->t);
  }
}

int A::EseqExp::MaxArgs() const {
  return std::max(this->stm->MaxArgs(), this->exp->MaxArgs());
}

IntAndTable *A::EseqExp::Interp(Table *t) const {
  return this->exp->Interp(this->stm->Interp(t)); //先执行stm，再执行exp
}
 
int A::PairExpList::MaxArgs() const {
  return 1 + this->tail->MaxArgs();
}

IntAndTable *A::PairExpList::Interp(Table *t) const {
  IntAndTable *expT = this->exp->Interp(t);
  printf("%d ", expT->i);
  return this->tail->Interp(expT->t);
}

int A::LastExpList::MaxArgs() const {
  return this->exp->MaxArgs();
}

IntAndTable *A::LastExpList::Interp(Table *t) const {
  IntAndTable *lastExpT = exp->Interp(t);
  printf("%d\n", lastExpT->i);
  return lastExpT;
}

int Table::Lookup(const std::string &key) const {
  if (id == key) {
    return value;
  } else if (tail != nullptr) {
    return tail->Lookup(key);
  } else {
    assert(false);
  }
}

Table *Table::Update(const std::string &key, int val) const {
  return new Table(key, val, this);
}
}  // namespace A
