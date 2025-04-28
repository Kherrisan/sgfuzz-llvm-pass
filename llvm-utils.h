#pragma once

#include "llvm/IR/DIBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Instructions.h"

#include "utils.h"

#include <string>
#include <regex>

using namespace llvm;

const DIFile *getFileFromScope(const DIScope *Scope);

std::string getLocation(const Instruction *I);

std::string getDITypeString(llvm::DIType *ty);

std::string canonicalizeTypedefDIType(llvm::DIType *&ty);

std::string pruneStructName(const std::string &structName);

int getTypeSizeInBits(Module *M, Type *ty);

std::string instructionValueName(Value *V);

Value *pruneBitfieldCasting(Value *V);

/**
 * 判断一个字符串是否是另一个字符串的前缀，并且除了前缀之后只有数字
 * @param prefix 前缀字符串
 * @param str 要检查的字符串
 * @return 如果满足条件返回true，否则返回false
 */
bool isPrefixWithOnlyDigits(const std::string &prefix, const std::string &str);

void printStructLayout(Module &M, std::string name);