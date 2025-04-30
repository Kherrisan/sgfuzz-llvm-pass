#include "llvm/Passes/PassBuilder.h"
#include "llvm/Passes/PassPlugin.h"

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/PassManager.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"

#include "llvm/IR/Instruction.h"
#include "llvm/IR/AbstractCallSite.h"
#include "llvm/IR/GlobalValue.h"

#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/CodeGen/MachineFunctionPass.h"

#include "llvm/IR/Intrinsics.h"

#include "llvm/Transforms/Utils.h"
#include <cstdio>
#include <llvm/IR/BasicBlock.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/Use.h>
#include <llvm/IR/Value.h>
#include <llvm/IR/Attributes.h>

#include <llvm/Transforms/Utils/ValueMapper.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IRReader/IRReader.h>

#include <cstdint>
#include <cstdlib>

#include <random>
#include <utility>
#include <vector>
#include <fstream>
#include <set>
#include <map>
#include <filesystem>
#include <string>
#include <regex>
#include <sys/mman.h>
#include <fcntl.h>
#include <unistd.h>
#include <optional>

#include "llvm/BinaryFormat/Dwarf.h"

#include "llvm-variable-resolver.h"

#define DEBUG_TYPE "sgfuzz-source-pass"
#define SGFUZZ_BLOCKING_TYPE_FILE_ENV "SGFUZZ_BLOCKING_TYPE_FILE"
#define SGFUZZ_PATCHING_TYPE_FILE_ENV "SGFUZZ_PATCHING_TYPE_FILE"

using namespace llvm;
using namespace std;
namespace fs = std::filesystem;

enum InstrumentType
{
    // The target instruction receive the variable to be patched as the variable
    // so the presence of the argument should be replaced with the patched one (mutated one)
    ARGS,
    // The target instruction generate the value which should be patched
    // so any user of this value should be replaced with the patched one (mutated one)
    OUTPUT
};

// static cl::opt<std::string> PatchingVariable("patching-variable", cl::desc("Specify the variable name and the source file name to be patched"), cl::value_desc("pvar"));

/*
We need the following capabilites:
    - The ability to mutate the values loaded/stored by load and store instructions.
    - Some way to trace which store/load instructions where executed in which order.
        - via. INT3 tracing?
        - via. patch point and custom stub that is called?
        - ?We need some RT to transfer the traces to the parent
*/
enum InsTy
{
    Random = 0,
    Load = 1,
    Store = 2,
    Add = 3,
    Sub = 4,
    Icmp = 5,
    Select = 6,
    Branch = 7,
    Switch = 8,
    Call = 9
};

const char *insTyStrings[] = {"RANDOM", "LOAD", "STORE", "ADD", "SUB", "ICMP", "SELECT", "BRANCH", "SWITCH", "CALL"};

enum InstrumentMethod
{
    STACK_SPILL,
    DIRECT
};

uint64_t get_alloction_size_in_bits(AllocaInst *ins, Value *target)
{
    if (target->getType()->isIntegerTy())
    {
        return target->getType()->getIntegerBitWidth();
    }
    else
    {
        return *ins->getAllocationSizeInBits(ins->getModule()->getDataLayout());
    }
}

/*
Split a string containing multiple comma-separated keywords
and return the set of these keywords
*/
std::vector<std::string> split_string(std::string s, char delim)
{
    size_t pos_start = 0, pos_end;
    std::string token;
    std::vector<std::string> res;

    while ((pos_end = s.find(delim, pos_start)) != std::string::npos)
    {
        token = s.substr(pos_start, pos_end - pos_start);
        pos_start = pos_end + 1;
        res.push_back(token);
    }

    res.push_back(s.substr(pos_start));
    return res;
}

/*
Check if an environment variable is set.
*/
bool env_var_set(const char *env_var)
{
    const char *envp = std::getenv(env_var);
    if (envp)
        return true;
    return false;
}

/*
Convert environment variable content to a set.
Expects comma-separated list of values in the env var.
*/
std::vector<std::string> parseEnvironmentList(const char *env_var)
{
    const char *envp = std::getenv(env_var);
    if (!envp)
        return std::vector<std::string>();
    return split_string(std::string(envp), /* delim = */ ',');
}

std::string addPrefixToFilename(const std::string &filePath, const std::string &prefix)
{
    fs::path pathObj(filePath);

    // 获取文件名和扩展名
    std::string filename = pathObj.filename().string();
    std::string newFilename = prefix + filename;

    // 构造新的路径
    fs::path newPath = pathObj.parent_path() / newFilename;

    return newPath.string();
}

class VariableInfo
{
public:
    unsigned int id;
    unsigned int svfgId;
    unsigned int pagId;
    unsigned int icfgId;
    Instruction *ins;
    InstrumentType type;
    InstrumentMethod method;
    Value *V;
    std::string fileName;
    unsigned int line;
    unsigned int col;
    std::string moduleName;
    std::string func;
    std::string insTy;
    pingu::VarInfo varInfo;
    std::string detail;
    string bbName;

    nlohmann::json to_json()
    {
        nlohmann::json jsonPP = {
            {"id", id},
            {"svfg_id", svfgId},
            {"pag_id", pagId},
            {"icfg_id", icfgId},
            {"module", moduleName},
            {"file", fileName},
            {"line", line},
            {"col", col},
            {"function", func},
            {"ins", ins->getOpcode()},
            {"method", (int)method},
            {"detail", detail},
            {"var", varInfo.to_json()},
            {"bb_name", bbName},
        };
        return jsonPP;
    }
};

class SGFuzzPass : public PassInfoMixin<SGFuzzPass>
{
public:
    SGFuzzPass();
    ~SGFuzzPass();

    PreservedAnalyses run(Module &M, ModuleAnalysisManager &);
    bool replaceMainFunction(Module &M);
    void record(vector<VariableInfo> &varInfoList, Instruction *I, InstrumentType type, Value *V, string ppTy, pingu::VarInfo &var_info, uint64_t id, string detail);
    bool scan(Module &M, FunctionCallee &instrument_fn);
    void dumpModuleToFile(const Module &M);
    bool handleStoreInstruction(Module &M, Function *F, StoreInst *SI, vector<VariableInfo> &patchPointInfoList);
    bool instrument(vector<VariableInfo> &patchPointInfoList, Module &M, Function *F, Function *stackmap_intr);
    bool shouldInstrument(pingu::VarInfo &varInfo);

private:
    vector<tuple<string, string>> patchingVariableWhiteList;
    set<Value *> instrumentedValues;

    int ppId;

    pingu::VarInfoResolver varResolver;
    vector<VariableInfo> varInfoList;

    vector<string> blockingTypes;
    vector<string> patchingTypes;
};

SGFuzzPass::SGFuzzPass()
{
    ENV_DEBUG(dbgs() << "SGFuzzPass()\n");

    ppId = 0;

    if (env_var_set("FT_BLACKLIST_FILES"))
    {
        for (std::string s : parseEnvironmentList("FT_BLACKLIST_FILES"))
        {
            blockingTypes.push_back(s);
        }
    }
}

SGFuzzPass::~SGFuzzPass()
{
    ENV_DEBUG(dbgs() << "~SGFuzzPass()\n");
}

PreservedAnalyses SGFuzzPass::run(Module &M, ModuleAnalysisManager &MAM)
{
    ENV_DEBUG(dbgs() << "FuzztructionSourcePass run on file: " << M.getSourceFileName() << "\n");

    std::error_code ErrorCode;
    std::string ModuleFileName = M.getSourceFileName() + ".sgfuzz.ll";
    raw_fd_ostream OutputFile(ModuleFileName, ErrorCode);
    M.print(OutputFile, NULL);
    OutputFile.close();

    if (std::find(blockingTypes.begin(), blockingTypes.end(), M.getSourceFileName()) != blockingTypes.end())
    {
        ENV_DEBUG(dbgs() << "FT: Ignore blacklist file: " << M.getSourceFileName() << "\n");
        return PreservedAnalyses::all();
    }

    if (env_var_set(SGFUZZ_BLOCKING_TYPE_FILE_ENV))
    {
        string blockingTypeFile = getenv(SGFUZZ_BLOCKING_TYPE_FILE_ENV);
        ifstream file(blockingTypeFile);
        string line;
        while (getline(file, line))
        {
            blockingTypes.push_back(line);
        }
        file.close();
    }

    if (env_var_set(SGFUZZ_PATCHING_TYPE_FILE_ENV))
    {
        string patchingTypeFile = getenv(SGFUZZ_PATCHING_TYPE_FILE_ENV);
        ifstream file(patchingTypeFile);
        string line;
        while (getline(file, line))
        {
            patchingTypes.push_back(line);
        }
        file.close();
    }
    else
    {
        dbgs() << "[x] sgfuzz-llvm-pass: No patching types specified, SGFUZZ_PATCHING_TYPE_FILE is not set !\n";
        assert(false && "No patching types specified !");
    }

    bool ModuleModified = false;

    varResolver.collectDITypes(M);

    auto instrumentFunc = M.getOrInsertFunction(
        "__sfuzzer_instrument",
        FunctionType::getVoidTy(M.getContext()),
        Type::getInt32Ty(M.getContext()), // state_name
        Type::getInt32Ty(M.getContext())  // state_value
    );

    if (getenv("SGFUZZ_USE_HF_MAIN"))
    {
        bool replaced = replaceMainFunction(M);
        if (!replaced)
        {
            assert(false && "Failed to replace main function");
        }
        ModuleModified = true;
    }

    ModuleModified |= scan(M, instrumentFunc);

    auto fileName = M.getSourceFileName() + ".sgfuzz.pp.json";
    ofstream varJsonFile(fileName);
    auto varJsonList = nlohmann::json::array();
    for (auto &pp : varInfoList)
    {
        varJsonList.push_back(pp.to_json());
    }
    varJsonFile << varJsonList.dump(4) << "\n";
    dbgs() << "[+] sgfuzz-llvm-pass: Instrumented " << varInfoList.size() << " variables in " << M.getSourceFileName() << "\n";
    varJsonFile.close();

    dbgs() << "[+] sgfuzz-llvm-pass: Dumping module to file\n";
    dumpModuleToFile(M);

    if (ModuleModified)
    {
        return PreservedAnalyses::none();
    }
    else
    {
        return PreservedAnalyses::all();
    }
}

string ins2ppTy(Instruction &I)
{
    if (auto *LI = dyn_cast<LoadInst>(&I))
    {
        return "LOAD";
    }
    else if (auto *store_op = dyn_cast<StoreInst>(&I))
    {
        return "STORE";
    }
    else if (I.getOpcode() == Instruction::Add)
    {
        return "ADD";
    }
    else if (I.getOpcode() == Instruction::Sub)
    {
        return "SUB";
    }
    else if (I.getOpcode() == Instruction::ICmp)
    {
        return "ICMP";
    }
    else if (I.getOpcode() == Instruction::Select)
    {
        return "SELECT";
    }
    else if (I.getOpcode() == Instruction::Br)
    {
        return "BRANCH";
    }
    else if (I.getOpcode() == Instruction::Switch)
    {
        return "SWITCH";
    }
    else
    {
        return "RANDOM";
    }
}

bool SGFuzzPass::shouldInstrument(pingu::VarInfo &varInfo)
{
    if (!blockingTypes.empty())
    {
        for (auto &bt : blockingTypes)
        {
            if (varInfo.type->kind() == pingu::Type::Kind::Int && varInfo.type->typedefName() == bt)
            {
                return false;
            }
            else if (varInfo.type->kind() == pingu::Type::Kind::Enum && static_cast<pingu::Enum *>(varInfo.type)->name() == bt)
            {
                return false;
            }
            else if (varInfo.type->kind() == pingu::Type::Kind::Pointer)
            {
                auto pointee = static_cast<pingu::Pointer *>(varInfo.type)->pointee();
                if (pointee->kind() == pingu::Type::Kind::Int && pointee->typedefName() == bt)
                {
                    return false;
                }
                else if (pointee->kind() == pingu::Type::Kind::Enum && static_cast<pingu::Enum *>(pointee)->name() == bt)
                {
                    return false;
                }
            }
        }
    }

    if (!patchingTypes.empty())
    {
        for (auto &pt : patchingTypes)
        {
            if (varInfo.type->kind() == pingu::Type::Kind::Int &&
                varInfo.type->typedefName() == pt)
            {
                return true;
            }
            else if (varInfo.type->kind() == pingu::Type::Kind::Enum && static_cast<pingu::Enum *>(varInfo.type)->name() == pt)
            {
                return true;
            }
            else if (varInfo.type->kind() == pingu::Type::Kind::Pointer)
            {
                auto pointee = static_cast<pingu::Pointer *>(varInfo.type)->pointee();
                if (pointee->typedefName() == pt)
                {
                    return true;
                }
                if (pointee->kind() == pingu::Type::Kind::Enum && static_cast<pingu::Enum *>(pointee)->name() == pt)
                {
                    return true;
                }
            }
        }
    }
    return false;
}

void SGFuzzPass::record(vector<VariableInfo> &patchPointInfoList, Instruction *I, InstrumentType type, Value *V, string ppTy, pingu::VarInfo &var_info, uint64_t id, string detail)
{
    VariableInfo info;
    info.ins = I;
    info.V = V;
    info.varInfo = var_info;
    info.id = id;
    info.insTy = ppTy;
    info.type = type;
    info.moduleName = I->getModule()->getName().str();
    info.detail = detail;
    info.bbName = I->getParent()->getName().str();

    if (auto *Loc = I->getDebugLoc().get())
    {
        info.line = Loc->getLine();
        info.col = Loc->getColumn();
        info.fileName = Loc->getFilename().str();
    }

    if (auto *Func = I->getFunction())
    {
        info.func = Func->getName().str();
    }

    instrumentedValues.insert(V);

    patchPointInfoList.push_back(info);
}

bool SGFuzzPass::instrument(vector<VariableInfo> &funcVarInfoList, Module &M, Function *F, Function *sgfuzz_instrument_fn)
{
    bool modified = false;
    for (auto &pp : funcVarInfoList)
    {
        // Create call to sgfuzz_instrument_fn
        llvm::IRBuilder Builder(pp.ins);
        Value *args[] = {
            Builder.getInt32(pp.id), // id
            pp.V                     // value
        };
        Builder.CreateCall(sgfuzz_instrument_fn, args);
        modified = true;

        varInfoList.push_back(pp);
    }

    funcVarInfoList.clear();

    return modified;
}

bool onlyUsedInMemCall(Value *V)
{
    if (Instruction *I = dyn_cast<Instruction>(V))
    {
        if (CallInst *CI = dyn_cast<CallInst>(I))
        {
            if (Function *F = CI->getCalledFunction())
            {
                string name = F->getName().str();
                if (name.find("memcpy") != string::npos || name.find("memset") != string::npos || name.find("memmove") != string::npos)
                {
                    return true;
                }
            }
        }
        else if (LoadInst *LI = dyn_cast<LoadInst>(I))
        {
            if (!LI->hasOneUser())
            {
                return false;
            }
            User *user = *LI->user_begin();
            return onlyUsedInMemCall(user);
        }
        else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I))
        {
            if (!GEP->hasOneUser())
            {
                return false;
            }
            User *user = *GEP->user_begin();
            return onlyUsedInMemCall(user);
        }
    }
    return false;
}

bool SGFuzzPass::handleStoreInstruction(Module &M, Function *F, StoreInst *SI, vector<VariableInfo> &patchPointInfoList)
{
    ENV_DEBUG(dbgs() << "Handling store: " << *SI << "\n");
    if (SI->getMetadata("nopatch"))
    {
        return false;
    }

    auto var = varResolver.resolveVarInfo(SI->getPointerOperand(), F);
    if (!var)
    {
        return false;
    }

    if (SI->getOperand(0)->getType()->isStructTy() || SI->getOperand(0)->getType()->isArrayTy())
    {
        return false;
    }

    auto operand = varResolver.interpret(&M, SI->getOperand(0)->getType(), *var);
    if (!operand)
    {
        return false;
    }
    ENV_DEBUG(dbgs() << "operand: " << operand->to_json().dump(4) << "\n");

    if (!shouldInstrument(*var))
    {
        return false;
    }
    dbgs() << "[+] sgfuzz-llvm-pass: Found a store operand to be instrumented: " << *SI << " -> " << var->type->toString() << "\n";

    if (!SI->getOperand(0)->getType()->isIntegerTy())
    {
        dbgs() << "[!] sgfuzz-llvm-pass: Skip this store operand due to the type is " << *SI->getOperand(0)->getType() << ", not integer\n";
        return false;
    }

    auto target = SI->getOperand(0);

    uint64_t id = ppId++;
    ENV_DEBUG(dbgs() << "Instrumenting store instruction: " << id << " " << *SI << "\n");

    // patching the operand of the store instruction, which is the SI->getOperand(0)
    record(patchPointInfoList, SI, InstrumentType::ARGS, target, "STORE", *operand, id, "");

    return true;
}

/*
Extract integer specified in environment variable.
*/
uint32_t parse_env_var_int(const char *env_var, uint32_t default_val)
{
    const char *envp = std::getenv(env_var);
    if (!envp)
        return default_val;
    uint32_t val = (uint32_t)std::stol(envp);
    return val;
}

bool SGFuzzPass::replaceMainFunction(Module &M)
{
    bool modified = false;
    for (auto &F : M)
    {
        if (F.getName() == "main")
        {
            F.setName("HonggfuzzNetDriver_main");
            dbgs() << "[+] sgfuzz-llvm-pass: Renamed main() to HonggfuzzNetDriver_main()\n";
            modified = true;
        }
    }
    return modified;
}

bool SGFuzzPass::scan(Module &M, FunctionCallee &instrument_fn)
{
    dbgs() << "[+] sgfuzz-llvm-pass: Scanning and instrumenting module\n";
    Value *instrument_fn_value = instrument_fn.getCallee();
    Function *instrument_fn_func = cast<Function>(instrument_fn_value);

    this->instrumentedValues = {};

    // Get functions which should not be called (i.e., for which we delete calls to)
    auto fn_del_vec = parseEnvironmentList("FT_NOP_FN");
    std::set<std::string> fn_del(fn_del_vec.begin(), fn_del_vec.end());
    ENV_DEBUG(dbgs() << "FT: Deleting function calls to " << fn_del.size() << " functions\n");

    // Track whether we modified the module
    int totalFuncs = M.getFunctionList().size();
    int progress = 0;
    bool modified = false;
    uint64_t num_patchpoints = 0;

    for (auto &F : M)
    {
        bool log_enabled_backup = ENV_LOG_ENABLED;

        if (totalFuncs > 10 && ++progress % (totalFuncs / 10) == 0)
            dbgs() << "[+] sgfuzz-llvm-pass: Functions instrumenting progress: " << progress << "/" << totalFuncs << "(" << (progress * 100 / totalFuncs) << "%)\n";

        ENV_DEBUG(dbgs() << "FT: Instrumenting function " << F.getName() << "\n");

        if (F.empty())
            continue;

        vector<VariableInfo> funcVarInfoList;

        for (auto &B : F)
        {
            if (B.empty())
                continue;

            for (BasicBlock::iterator DI = B.begin(); DI != B.end();)
            {
                if (auto *SI = dyn_cast<StoreInst>(&*DI++))
                {
                    if (handleStoreInstruction(M, &F, SI, funcVarInfoList))
                    {
                        modified = true;
                        num_patchpoints++;
                    }
                }
            }
        }

        instrument(funcVarInfoList, M, &F, instrument_fn_func);

        ENV_LOG_ENABLED = log_enabled_backup;
    }
    LLVM_DEBUG(ENV_DEBUG(dbgs() << "FT: Inserted " << num_patchpoints << " patchpoints\n"));

    return modified;
}

void registerCallbacks(PassBuilder &PB)
{
    PB.registerOptimizerLastEPCallback(
        [&](ModulePassManager &MPM, OptimizationLevel)
        {
            // used in clang -fpass-plugin=libFuzztructionSourcePass.so -O0(or other optimization level)
            MPM.addPass(SGFuzzPass());
        });
    PB.registerPipelineParsingCallback(
        [&](StringRef Name, ModulePassManager &MPM, ArrayRef<PassBuilder::PipelineElement>)
        {
            // used in opt -load-pass-plugin=libSGFuzzSourcePass.so -passes="sgfuzz-source"
            if (Name == "sgfuzz-source")
            {
                MPM.addPass(SGFuzzPass());
                return true;
            }
            return false;
        });
}

extern "C" ::llvm::PassPluginLibraryInfo LLVM_ATTRIBUTE_WEAK
llvmGetPassPluginInfo()
{
    return {
        LLVM_PLUGIN_API_VERSION, "FuzztructionSourcePass", "v0.1",
        registerCallbacks};
}

void SGFuzzPass::dumpModuleToFile(const Module &M)
{
    std::error_code ErrorCode;
    std::string ModuleFileName = M.getSourceFileName() + ".sgfuzz.patched.ll";
    raw_fd_ostream OutputFile(ModuleFileName, ErrorCode);
    M.print(OutputFile, NULL);
    OutputFile.close();
}