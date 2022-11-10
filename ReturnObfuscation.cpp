#include "FuncHelper.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Alignment.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <fstream>
#include <string>
using namespace llvm;

namespace {
struct ReturnObfuscation : public FunctionPass {
  static char ID;
  ReturnObfuscation() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    DebugLoc deb;
    for (auto &BB : F) {
      for (auto &I : BB) {
        deb = I.getDebugLoc();
        break;
      }
      break;
    }
    int num_this_function;
    int count;
    size_t num_retblocks;
    Module *mod = F.getParent();

    std::vector<Constant *> retblocks;
    // 함수 가져오기
    std::ifstream function_list;
    function_list.open("functions.txt");
    std::vector<Function *> functions;
    std::vector<Function *> functions2;
    std::string line;
    while (getline(function_list, line)) {
      functions.push_back(mod->getFunction(line));
    }
    count = 0;
    bool inserted = false;
    StructType *ty_struct_ctx = mod->getTypeByName("struct.AES_ctx");
    errs() << ty_struct_ctx->getName() << "\n";

    // 함수 별로 벡터에 집어넣기
    for (auto &Fn : functions) {
      inserted = false;
      for (auto &BB : (*Fn)) {
        if (BB.getName().equals("obfuscatedreturn")) {
          Constant *retBlockAddress = BlockAddress::get(&BB);
          retblocks.push_back(retBlockAddress);
          if (!inserted)
            functions2.push_back(Fn);
          inserted = true;
        }
      }
    }

    for (auto &Fn : functions2) {
      if (Fn->getName().equals(F.getName())) {
        errs() << "GOOD Num this function " << Fn->getName() << "\n";
        num_this_function = count;
      }
      count++;
    }
    num_retblocks = retblocks.size();

    ArrayType *array_in =
        ArrayType::get(IntegerType::get(mod->getContext(), 8), 36);
    ArrayType *array_keyiv =
        ArrayType::get(IntegerType::get(mod->getContext(), 8), 16);
    ArrayType *array_out = ArrayType::get(array_in, num_retblocks);
    ArrayType *array_retblock = ArrayType::get(
        PointerType::get(IntegerType::get(mod->getContext(), 8), 0),
        num_retblocks);
    PointerType *array_ptr = PointerType::get(array_out, 0);
    ConstantInt *const_int_0 = ConstantInt::get(
        mod->getContext(), APInt(32, StringRef(std::to_string(0)), 10));
    ConstantInt *const_int_1 = ConstantInt::get(
        mod->getContext(), APInt(32, StringRef(std::to_string(1)), 10));
    ConstantInt *const_int_array_out = ConstantInt::get(
        mod->getContext(),
        APInt(32, StringRef(std::to_string(num_retblocks)), 10));
    ConstantInt *const_int_array_in = ConstantInt::get(
        mod->getContext(), APInt(32, StringRef(std::to_string(36)), 10));
    ConstantInt *const_int_xordata = ConstantInt::get(
        mod->getContext(), APInt(32, StringRef(std::to_string(0x33)), 10));

    std::vector<Type *> Func_deobfus_type_args;
    FunctionType *Func_deobfus_type = FunctionType::get(
        IntegerType::get(mod->getContext(), 32), Func_deobfus_type_args, false);

    Function *Func_deobfus = mod->getFunction("init_module");
    if (!Func_deobfus) {
      Func_deobfus = Function::Create(
          Func_deobfus_type, GlobalValue::ExternalLinkage, "init_module", mod);
      Func_deobfus->setCallingConv(CallingConv::C);
    }
    AttributeList Func_deobfus_att_list;
    SmallVector<AttributeList, 4> Attrs;
    AttributeList PAS;
    AttrBuilder B;
    B.addAttribute(Attribute::AlwaysInline);
    B.addAttribute(Attribute::NoRecurse);
    B.addAttribute(Attribute::NoUnwind);
    PAS = AttributeList::get(mod->getContext(), ~0U, B);
    Attrs.push_back(PAS);
    Func_deobfus_att_list = AttributeList::get(mod->getContext(), Attrs);
    Func_deobfus->setAttributes(Func_deobfus_att_list);

    if (Func_deobfus->size() == 0) {

      PointerType *ret_func_ptr[10000];
      AllocaInst *ptr_this_ret[10000];
      StoreInst *void_17[10000];
      uint8_t key[16] = {
          (uint8_t)0x2b, (uint8_t)0x7e, (uint8_t)0x15, (uint8_t)0x16,
          (uint8_t)0x28, (uint8_t)0xae, (uint8_t)0xd2, (uint8_t)0xa6,
          (uint8_t)0xab, (uint8_t)0xf7, (uint8_t)0x15, (uint8_t)0x88,
          (uint8_t)0x09, (uint8_t)0xcf, (uint8_t)0x4f, (uint8_t)0x3c};
      uint8_t iv[16] = {0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7,
                        0xf8, 0xf9, 0xfa, 0xfb, 0xfc, 0xfd, 0xfe, 0xff};
      std::vector<Constant *> keyEntries;
      std::vector<Constant *> ivEntries;
      for (int i = 0; i < 16; i++) {
        keyEntries.push_back(
            ConstantInt::get(mod->getContext(),
                             APInt(8, StringRef(std::to_string(key[i])), 10)));
      }
      for (int i = 0; i < 16; i++) {
        ivEntries.push_back(ConstantInt::get(
            mod->getContext(), APInt(8, StringRef(std::to_string(iv[i])), 10)));
      }

      GlobalVariable *gvar_key =
          new GlobalVariable(*mod, array_keyiv, false,
                             GlobalValue::ExternalLinkage, 0, "aes_key_ir");
      gvar_key->setAlignment(Align(16));
      gvar_key->setInitializer(ConstantArray::get(array_keyiv, keyEntries));

      GlobalVariable *gvar_iv =
          new GlobalVariable(*mod, array_keyiv, false,
                             GlobalValue::ExternalLinkage, 0, "aes_iv_ir");
      gvar_iv->setAlignment(Align(16));
      gvar_iv->setInitializer(ConstantArray::get(array_keyiv, ivEntries));

      GlobalVariable *gvar_ret_inst_list =
          new GlobalVariable(*mod, array_out, false, GlobalValue::CommonLinkage,
                             0, "ret_inst_list");
      gvar_ret_inst_list->setAlignment(Align(16));
      ConstantAggregateZero *const_array_6 =
          ConstantAggregateZero::get(array_out);
      gvar_ret_inst_list->setInitializer(const_array_6);
      // TODO : 없애기
      /*
      GlobalVariable *gvar_array_retblock =
          new GlobalVariable(*mod, array_retblock, false,
                             GlobalValue::ExternalLinkage, 0, "array_retblock");
      gvar_array_retblock->setAlignment(Align(16));
      */

      GlobalVariable *gvar_array_retblock =
          new GlobalVariable(*mod, array_retblock, false,
                             GlobalValue::CommonLinkage, 0, "array_retblock");
      gvar_array_retblock->setAlignment(Align(16));
      // TODO 고치기

      ConstantAggregateZero *const_array_7 =
          ConstantAggregateZero::get(array_retblock);
      gvar_array_retblock->setInitializer(const_array_7);
      BasicBlock *obfus_entry =
          BasicBlock::Create(mod->getContext(), "entry", Func_deobfus);
      BasicBlock *for_i_cond =
          BasicBlock::Create(mod->getContext(), "i_cond", Func_deobfus);
      // BasicBlock *for_j_init =
      //    BasicBlock::Create(mod->getContext(), "j_init", Func_deobfus);
      // BasicBlock *for_j_cond =
      //    BasicBlock::Create(mod->getContext(), "j_cond", Func_deobfus);
      // BasicBlock *for_i_j =
      //    BasicBlock::Create(mod->getContext(), "i_j", Func_deobfus);
      // BasicBlock *for_j_add =
      //    BasicBlock::Create(mod->getContext(), "j_add", Func_deobfus);
      BasicBlock *for_i =
          BasicBlock::Create(mod->getContext(), "i", Func_deobfus);
      BasicBlock *for_i_add =
          BasicBlock::Create(mod->getContext(), "i_add", Func_deobfus);

      BasicBlock *for_i_end =
          BasicBlock::Create(mod->getContext(), "i_end", Func_deobfus);
      std::vector<Constant *> const_ptr_blocks;
      /*
      std::vector<Value *> putchar_arguments2;
      putchar_arguments2.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("75"), 10)));
      ArrayRef<Value *> putchar_CallArgs2 =
          ArrayRef<Value *>(putchar_arguments2);

      Function *Func_putchar2 = mod->getFunction("putchar");
      CallInst *Func_putchar_call2 = CallInst::Create(
          Func_putchar2, putchar_CallArgs2, "", obfus_entry);
      Func_putchar_call2->setCallingConv(CallingConv::C);
      Func_putchar_call2->setTailCall(false);
      AttributeList Func_putchar_call_PAL2;
      Func_putchar_call2->setAttributes(Func_putchar_call_PAL2);

      std::vector<Value *> putchar_arguments5;
      putchar_arguments5.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("10"), 10)));
      ArrayRef<Value *> putchar_CallArgs5 =
          ArrayRef<Value *>(putchar_arguments5);

      Function *Func_putchar5 = mod->getFunction("putchar");
      CallInst *Func_putchar_call5 = CallInst::Create(
          Func_putchar5, putchar_CallArgs5, "", obfus_entry);
      Func_putchar_call5->setCallingConv(CallingConv::C);
      Func_putchar_call5->setTailCall(false);
      AttributeList Func_putchar_call_PAL5;
      Func_putchar_call5->setAttributes(Func_putchar_call_PAL5);
    */
      Type *ty_keyiv =
          ArrayType::get(IntegerType::get(mod->getContext(), 8), 16);
      AllocaInst *key_alloc =
          new AllocaInst(ty_keyiv, NULL, "key_alloc", obfus_entry);
      AllocaInst *iv_alloc =
          new AllocaInst(ty_keyiv, NULL, "iv_alloc", obfus_entry);
      BitCastInst *key_bitcast = new BitCastInst(
          key_alloc,
          PointerType::get(IntegerType::get(mod->getContext(), 8), 0),
          "key_bitcast", obfus_entry);
      BitCastInst *iv_bitcast = new BitCastInst(
          iv_alloc, PointerType::get(IntegerType::get(mod->getContext(), 8), 0),
          "iv_bitcast", obfus_entry);

      Function *Func_FMC_Open = mod->getFunction("FMC_Open");

      CallInst *call_open = CallInst::Create(Func_FMC_Open, "", obfus_entry);
      call_open->setCallingConv(CallingConv::C);
      call_open->setTailCall(false);
      AttributeList Func_FMC_Open_PAL;
      call_open->setAttributes(Func_FMC_Open_PAL);

      std::vector<Value *> key_4_ptrlist = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)),
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("4"), 10))};

      std::vector<Value *> key_8_ptrlist = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)),
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("8"), 10))};

      std::vector<Value *> key_12_ptrlist = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)),
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("12"), 10))};

      GetElementPtrInst *key_4_element = GetElementPtrInst::Create(
          ty_keyiv, key_alloc, key_4_ptrlist, "", obfus_entry);

      GetElementPtrInst *key_8_element = GetElementPtrInst::Create(
          ty_keyiv, key_alloc, key_8_ptrlist, "", obfus_entry);

      GetElementPtrInst *key_12_element = GetElementPtrInst::Create(
          ty_keyiv, key_alloc, key_12_ptrlist, "", obfus_entry);

      BitCastInst *key_bit_0 = new BitCastInst(
          key_alloc,
          PointerType::get(IntegerType::get(mod->getContext(), 32), 0), "key_0",
          obfus_entry);
      BitCastInst *key_bit_4 = new BitCastInst(
          key_4_element,
          PointerType::get(IntegerType::get(mod->getContext(), 32), 0), "key_4",
          obfus_entry);
      BitCastInst *key_bit_8 = new BitCastInst(
          key_8_element,
          PointerType::get(IntegerType::get(mod->getContext(), 32), 0), "key_8",
          obfus_entry);
      BitCastInst *key_bit_12 = new BitCastInst(
          key_12_element,
          PointerType::get(IntegerType::get(mod->getContext(), 32), 0),
          "key_12", obfus_entry);

      std::vector<Value *> key_arg_0 = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)),
          key_bit_0, key_bit_4};
      std::vector<Value *> key_arg_1 = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("1"), 10)),
          key_bit_8, key_bit_12};

      Function *Func_Read_OTP = mod->getFunction("FMC_Read_OTP");

      CallInst *Func_Read_OTP_Call_1 =
          CallInst::Create(Func_Read_OTP, key_arg_0, "", obfus_entry);
      Func_Read_OTP_Call_1->setCallingConv(CallingConv::C);
      Func_Read_OTP_Call_1->setTailCall(false);
      AttributeList Func_Read_OTP_Call_1_PAL;
      Func_Read_OTP_Call_1->setAttributes(Func_Read_OTP_Call_1_PAL);

      CallInst *Func_Read_OTP_Call_2 =
          CallInst::Create(Func_Read_OTP, key_arg_1, "", obfus_entry);
      Func_Read_OTP_Call_2->setCallingConv(CallingConv::C);
      Func_Read_OTP_Call_2->setTailCall(false);
      AttributeList Func_Read_OTP_Call_2_PAL;
      Func_Read_OTP_Call_2->setAttributes(Func_Read_OTP_Call_2_PAL);

      std::vector<Value *> iv_4_ptrlist = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)),
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("4"), 10))};

      std::vector<Value *> iv_8_ptrlist = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)),
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("8"), 10))};

      std::vector<Value *> iv_12_ptrlist = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)),
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("12"), 10))};

      GetElementPtrInst *iv_4_element = GetElementPtrInst::Create(
          ty_keyiv, iv_alloc, iv_4_ptrlist, "", obfus_entry);

      GetElementPtrInst *iv_8_element = GetElementPtrInst::Create(
          ty_keyiv, iv_alloc, iv_8_ptrlist, "", obfus_entry);

      GetElementPtrInst *iv_12_element = GetElementPtrInst::Create(
          ty_keyiv, iv_alloc, iv_12_ptrlist, "", obfus_entry);

      BitCastInst *iv_bit_0 = new BitCastInst(
          iv_alloc,
          PointerType::get(IntegerType::get(mod->getContext(), 32), 0), "iv_0",
          obfus_entry);
      BitCastInst *iv_bit_4 = new BitCastInst(
          iv_4_element,
          PointerType::get(IntegerType::get(mod->getContext(), 32), 0), "iv_4",
          obfus_entry);
      BitCastInst *iv_bit_8 = new BitCastInst(
          iv_8_element,
          PointerType::get(IntegerType::get(mod->getContext(), 32), 0), "iv_08",
          obfus_entry);
      BitCastInst *iv_bit_12 = new BitCastInst(
          iv_12_element,
          PointerType::get(IntegerType::get(mod->getContext(), 32), 0), "iv_12",
          obfus_entry);

      std::vector<Value *> iv_arg_0 = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)),
          iv_bit_0, iv_bit_4};
      std::vector<Value *> iv_arg_1 = {
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("1"), 10)),
          iv_bit_8, iv_bit_8};

      CallInst *Func_Read_OTP_Call_3 =
          CallInst::Create(Func_Read_OTP, iv_arg_0, "", obfus_entry);
      Func_Read_OTP_Call_3->setCallingConv(CallingConv::C);
      Func_Read_OTP_Call_3->setTailCall(false);
      AttributeList Func_Read_OTP_Call_3_PAL;
      Func_Read_OTP_Call_3->setAttributes(Func_Read_OTP_Call_3_PAL);

      CallInst *Func_Read_OTP_Call_4 =
          CallInst::Create(Func_Read_OTP, iv_arg_1, "", obfus_entry);
      Func_Read_OTP_Call_4->setCallingConv(CallingConv::C);
      Func_Read_OTP_Call_4->setTailCall(false);
      AttributeList Func_Read_OTP_Call_4_PAL;
      Func_Read_OTP_Call_4->setAttributes(Func_Read_OTP_Call_4_PAL);

      AllocaInst *ptr_ctx =
          new AllocaInst(ty_struct_ctx, NULL, "ctx", obfus_entry);
      ptr_ctx->setAlignment(Align(1));
      PointerType *ty_ptr_ctx = PointerType::get(ty_struct_ctx, 0);
      /*
      std::vector<Value *> get_AES_ctx_ptr_indices;
      get_AES_ctx_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      get_AES_ctx_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      get_AES_ctx_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      Instruction *get_AES_ctx_ptr = GetElementPtrInst::Create(
          ty_struct_ctx, ptr_ctx, get_AES_ctx_ptr_indices, "", obfus_entry);

      std::vector<Value *> get_AES_key_ptr_indices;
      get_AES_key_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      get_AES_key_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      Instruction *get_AES_key_ptr = GetElementPtrInst::Create(
          array_keyiv, gvar_key, get_AES_key_ptr_indices, "", obfus_entry);

      std::vector<Value *> get_AES_key_iv_indices;
      get_AES_key_iv_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      get_AES_key_iv_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      Instruction *get_AES_iv_ptr = GetElementPtrInst::Create(
          array_keyiv, gvar_iv, get_AES_key_iv_indices, "", obfus_entry);

      std::vector<Value *> aes_init_ctx_iv_arguments;
      aes_init_ctx_iv_arguments.push_back(ptr_ctx);
      aes_init_ctx_iv_arguments.push_back(get_AES_key_ptr);
      aes_init_ctx_iv_arguments.push_back(get_AES_iv_ptr);
      ArrayRef<Value *> aes_init_ctx_iv_CallArgs =
          ArrayRef<Value *>(aes_init_ctx_iv_arguments);

      Function *Func_AES_init_ctx_iv = mod->getFunction("AES_init_ctx_iv");
      CallInst *Func_AES_init_ctx_iv_call = CallInst::Create(
          Func_AES_init_ctx_iv, aes_init_ctx_iv_CallArgs, "", obfus_entry);
      Func_AES_init_ctx_iv_call->setCallingConv(CallingConv::C);
      Func_AES_init_ctx_iv_call->setTailCall(false);
      AttributeList Func_AES_init_ctx_iv_call_PAL;
      Func_AES_init_ctx_iv_call->setAttributes(Func_AES_init_ctx_iv_call_PAL);
    */

      for (size_t i = 0; i < num_retblocks; i++) {
        // Constant* const_blockaddress = BlockAddress::get(ret)
        // TODO: 꼭해야함
        // const_ptr_blocks.push_back(retblocks[i]);

        std::vector<Constant *> const_ptr_16_indices;
        const_ptr_16_indices.push_back(
            ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));
        const_ptr_16_indices.push_back(ConstantInt::get(
            mod->getContext(), APInt(64, StringRef(std::to_string(i)), 10)));
        Constant *const_ptr_16 = ConstantExpr::getGetElementPtr(
            array_retblock, gvar_array_retblock, const_ptr_16_indices);
        StoreInst *store_good =
            new StoreInst(retblocks[i], const_ptr_16, false, obfus_entry);
        store_good->setAlignment(Align(16));

        /*
        std::vector<Value *> get_retblock_array_indices;
        get_retblock_array_indices.push_back(const_int_0);
        get_retblock_array_indices.push_back(ConstantInt::get(
            mod->getContext(), APInt(32, StringRef(std::to_string(i)), 10)));
        Instruction *get_retblock = GetElementPtrInst::Create(
            array_retblock, gvar_array_retblock, get_retblock_array_indices, "",
            obfus_entry);
        LoadInst *load_ret_block_arr =
            new LoadInst(get_retblock, "", false, obfus_entry);
        */
        /*
        ret_func_ptr[i] =
            PointerType::get(IntegerType::get(mod->getContext(), 8), 0);
        ptr_this_ret[i] =
            new AllocaInst(ret_func_ptr[i], NULL, "ptr", obfus_entry);
        ;
        */
        // void_17[i] =
        //    new StoreInst(retblocks[i], get_retblock, false, obfus_entry);
      }

      // TODO : 없애기
      /*
      Constant* array_ret_blocks_const = ConstantArray::get(array_retblock,
      const_ptr_blocks);
      gvar_array_retblock->setInitializer(array_ret_blocks_const);
      */

      // %i = alloca i32, align 4
      AllocaInst *ptr_i = new AllocaInst(
          IntegerType::get(mod->getContext(), 32), NULL, "i", obfus_entry);
      // %j = alloca i32, align 4
      // AllocaInst *ptr_j = new AllocaInst(
      //    IntegerType::get(mod->getContext(), 32), NULL, "j", obfus_entry);
      StoreInst *str_i_0_1 =
          new StoreInst(const_int_0, ptr_i, false, obfus_entry);
      str_i_0_1->setAlignment(Align(4));
      // br label %i_cond
      BranchInst::Create(for_i_cond, obfus_entry);

      // for_i_cond
      // %4 = load i32* %i, align 4
      LoadInst *load_i_1 = new LoadInst(IntegerType::get(mod->getContext(), 32),
                                        ptr_i, "", false, for_i_cond);
      load_i_1->setAlignment(Align(4));
      // %5 = icmp slt i32 %4, 50
      ICmpInst *i_cmp_1 = new ICmpInst(*for_i_cond, ICmpInst::ICMP_SLT,
                                       load_i_1, const_int_array_out, "");
      // br i1 %5, label %for_j_init, for_i_end
      // BranchInst::Create(for_j_init, for_i_end, i_cmp_1, for_i_cond);
      BranchInst::Create(for_i, for_i_end, i_cmp_1, for_i_cond);

      /*
            // for_j_init
            StoreInst *str_j_0_1 =
                new StoreInst(const_int_0, ptr_j, false, for_j_init);
            str_j_0_1->setAlignment(Align(4));
            BranchInst::Create(for_j_cond, for_j_init);

            // for_j_cond
            LoadInst *load_j_1 = new
         LoadInst(IntegerType::get(mod->getContext(), 32), ptr_j, "", false,
         for_j_cond); load_j_1->setAlignment(Align(4));
            // %5 = icmp slt i32 %4, 50
            ICmpInst *j_cmp_1 = new ICmpInst(*for_j_cond, ICmpInst::ICMP_SLT,
                                             load_j_1, const_int_array_in, "");
            // br i1 %5, label %for_j_init, for_i_end
            BranchInst::Create(for_i_j, for_i, j_cmp_1, for_j_cond);

            // for_i_j
            LoadInst *load_i_addc = new LoadInst(
                IntegerType::get(mod->getContext(), 32), ptr_i, "", false,
         for_i_j); load_i_addc->setAlignment(Align(4)); CastInst *casted_i_addc
         = new SExtInst( load_i_addc, IntegerType::get(mod->getContext(), 64),
         "", for_i_j);

            std::vector<Value *> get_retblock_index_ptr_indices;
            get_retblock_index_ptr_indices.push_back(
                ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"),
         10))); get_retblock_index_ptr_indices.push_back(casted_i_addc);
            Instruction *get_retblock_index_ptr = GetElementPtrInst::Create(
                array_retblock, gvar_array_retblock,
         get_retblock_index_ptr_indices,
                "", for_i_j);

            LoadInst *load_retblock_ptr = new LoadInst(
                PointerType::get(IntegerType::get(mod->getContext(), 8), 0),
                get_retblock_index_ptr, "", false, for_i_j);
            load_retblock_ptr->setAlignment(Align(8));

            LoadInst *load_j_addc = new LoadInst(
                IntegerType::get(mod->getContext(), 32), ptr_j, "", false,
         for_i_j); load_j_addc->setAlignment(Align(4));

            CastInst *casted_j_addc = new SExtInst(
                load_j_addc, IntegerType::get(mod->getContext(), 64), "",
         for_i_j);

            std::vector<Value *> get_retblock_index_ptr_value_indices;
            get_retblock_index_ptr_value_indices.push_back(casted_j_addc);
            Instruction *get_retblock_index_ptr_value =
         GetElementPtrInst::Create( IntegerType::get(mod->getContext(), 8),
         load_retblock_ptr, get_retblock_index_ptr_value_indices, "", for_i_j);

            LoadInst *load_retblock_index_ptr_value =
                new LoadInst(IntegerType::get(mod->getContext(), 8),
                             get_retblock_index_ptr_value, "", false, for_i_j);
            load_retblock_index_ptr_value->setAlignment(Align(1)); // %5

            LoadInst *load_i_kkbc = new LoadInst(
                IntegerType::get(mod->getContext(), 32), ptr_i, "", false,
         for_i_j); load_i_kkbc->setAlignment(Align(4)); // 6 CastInst
         *casted_i_kkbc = new SExtInst(load_i_kkbc,
         IntegerType::get(mod->getContext(), 64), "", for_i_j); // idxprom6

            std::vector<Value *> get_ret_inst_ptr_indices;
            get_ret_inst_ptr_indices.push_back(
                ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"),
         10))); get_ret_inst_ptr_indices.push_back(casted_i_kkbc);

            Instruction *get_ret_inst_ptr = GetElementPtrInst::Create(
                array_out, gvar_ret_inst_list, get_ret_inst_ptr_indices, "",
                for_i_j); // arrayidx7
            LoadInst *load_j_kkbc = new LoadInst(
                IntegerType::get(mod->getContext(), 32), ptr_j, "", false,
         for_i_j); load_j_kkbc->setAlignment(Align(4)); // 7 CastInst
         *casted_j_kkbc = new SExtInst(load_j_kkbc,
         IntegerType::get(mod->getContext(), 64), "", for_i_j); // idxprom8

            std::vector<Value *> get_ret_inst_ptr_value_indices;
            get_ret_inst_ptr_value_indices.push_back(
                ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"),
         10))); get_ret_inst_ptr_value_indices.push_back(casted_j_kkbc);
            Instruction *get_ret_inst_ptr_value = GetElementPtrInst::Create(
                array_in, get_ret_inst_ptr, get_ret_inst_ptr_value_indices, "",
                for_i_j); // arrayidx9

            StoreInst *store_data =
                new StoreInst(load_retblock_index_ptr_value,
         get_ret_inst_ptr_value, false, for_i_j);
            store_data->setAlignment(Align(1));

            LoadInst *load_i_arrd = new LoadInst(
                IntegerType::get(mod->getContext(), 32), ptr_i, "", false,
         for_i_j); load_i_arrd->setAlignment(Align(4)); // 8 CastInst
         *casted_i_arrd = new SExtInst(load_i_arrd,
         IntegerType::get(mod->getContext(), 64), "", for_i_j); // idxprom10

            std::vector<Value *> get_ret_inst_ptr_indices2;
            get_ret_inst_ptr_indices2.push_back(
                ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"),
         10))); get_ret_inst_ptr_indices2.push_back(casted_i_arrd); Instruction
         *get_ret_inst_ptr2 = GetElementPtrInst::Create( array_out,
         gvar_ret_inst_list, get_ret_inst_ptr_indices2, "", for_i_j); //
         arrayidx7

            LoadInst *load_j_arrd = new LoadInst(
                IntegerType::get(mod->getContext(), 32), ptr_j, "", false,
         for_i_j); load_j_arrd->setAlignment(Align(4)); // 9 CastInst
         *casted_j_arrd = new SExtInst(load_j_arrd,
         IntegerType::get(mod->getContext(), 64), "", for_i_j); // idxprom12

            std::vector<Value *> get_ret_inst_ptr_value_indices2;
            get_ret_inst_ptr_value_indices2.push_back(
                ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"),
         10))); get_ret_inst_ptr_value_indices2.push_back(casted_j_arrd);
            Instruction *get_ret_inst_ptr_value2 = GetElementPtrInst::Create(
                array_in, get_ret_inst_ptr2, get_ret_inst_ptr_value_indices2,
         "", for_i_j); // arrayidx13

            LoadInst *load_ret_inst_value =
                new LoadInst(IntegerType::get(mod->getContext(), 8),
                             get_ret_inst_ptr_value2, "", false, for_i_j);
            load_ret_inst_value->setAlignment(Align(1)); // 10

            LoadInst *load_i_kera = new LoadInst(
                IntegerType::get(mod->getContext(), 32), ptr_i, "", false,
         for_i_j); load_i_kera->setAlignment(Align(4)); // 11 CastInst
         *casted_i_kera = new SExtInst(load_i_kera,
         IntegerType::get(mod->getContext(), 64), "", for_i_j); // idxprom15

            std::vector<Value *> get_ret_inst_ptr_indices3;
            get_ret_inst_ptr_indices3.push_back(
                ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"),
         10))); get_ret_inst_ptr_indices3.push_back(casted_i_kera); Instruction
         *get_ret_inst_ptr3 = GetElementPtrInst::Create( array_out,
         gvar_ret_inst_list, get_ret_inst_ptr_indices3, "", for_i_j); //
         arrayidx16

            LoadInst *load_j_kera = new LoadInst(
                IntegerType::get(mod->getContext(), 32), ptr_j, "", false,
         for_i_j); load_j_kera->setAlignment(Align(4)); // 12 CastInst
         *casted_j_kera = new SExtInst(load_j_kera,
         IntegerType::get(mod->getContext(), 64), "", for_i_j); // idxprom17

            std::vector<Value *> get_ret_inst_ptr_value_indices3;
            get_ret_inst_ptr_value_indices3.push_back(
                ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"),
         10))); get_ret_inst_ptr_value_indices3.push_back(casted_j_kera);
            Instruction *get_ret_inst_ptr_value3 = GetElementPtrInst::Create(
                array_in, get_ret_inst_ptr3, get_ret_inst_ptr_value_indices3,
         "", for_i_j); // arrayidx18

            StoreInst *store_xor_data = new StoreInst(
                load_ret_inst_value, get_ret_inst_ptr_value3, false, for_i_j);
            store_xor_data->setAlignment(Align(1));

            BranchInst::Create(for_j_add, for_i_j);
            // BranchInst::Create(for_i_add, for_j_init);
            // for_j_add

            LoadInst *load_j_5 = new
         LoadInst(IntegerType::get(mod->getContext(), 32), ptr_j, "", false,
         for_j_add); load_j_5->setAlignment(Align(4)); BinaryOperator *add_j_1 =
         BinaryOperator::Create( Instruction::Add, load_j_5, const_int_1, "",
         for_j_add); StoreInst *void_56 = new StoreInst(add_j_1, ptr_j, false,
         for_j_add); void_56->setAlignment(Align(4));
            BranchInst::Create(for_j_cond, for_j_add);
          */
      // for_i

      /*
            AllocaInst *ptr_ctx = new AllocaInst(ty_struct_ctx, NULL, "ctx",
         for_i); ptr_ctx->setAlignment(Align(1)); PointerType *ty_ptr_ctx =
         PointerType::get(ty_struct_ctx, 0);
      */

      CastInst *casted_i_addc = new SExtInst(
          load_i_1, IntegerType::get(mod->getContext(), 64), "", for_i);

      std::vector<Value *> get_retblock_index_ptr_indices;
      get_retblock_index_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));
      get_retblock_index_ptr_indices.push_back(casted_i_addc);
      Instruction *get_retblock_index_ptr =
          GetElementPtrInst::Create(array_retblock, gvar_array_retblock,
                                    get_retblock_index_ptr_indices, "", for_i);

      std::vector<Value *> get_ret_inst_ptr_indices;
      get_ret_inst_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));
      get_ret_inst_ptr_indices.push_back(casted_i_addc);

      Instruction *get_ret_inst_ptr = GetElementPtrInst::Create(
          array_out, gvar_ret_inst_list, get_ret_inst_ptr_indices, "",
          for_i); // arrayidx7

      std::vector<Value *> get_ret_inst_ptr_indices1;
      get_ret_inst_ptr_indices1.push_back(
          ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));
      get_ret_inst_ptr_indices1.push_back(
          ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));

      Instruction *get_ret_inst_ptr1 = GetElementPtrInst::Create(
          array_in, get_ret_inst_ptr, get_ret_inst_ptr_indices1, "",
          for_i); // arrayidx7

      LoadInst *ldr_retbl = new LoadInst(
          PointerType::get(IntegerType::get(mod->getContext(), 8), 0),
          get_retblock_index_ptr, "", for_i);

      std::vector<Value *> mcopyfunc_arguments;
      mcopyfunc_arguments.push_back(get_ret_inst_ptr1);
      mcopyfunc_arguments.push_back(ldr_retbl);
      mcopyfunc_arguments.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("32"), 10)));
      ArrayRef<Value *> mcopyfunc_arguments_CallArgs =
          ArrayRef<Value *>(mcopyfunc_arguments);
      get_ret_inst_ptr1->getType()->dump();
      ldr_retbl->getType()->dump();
      Function *mcopyfunc = mod->getFunction("mcpy");
      mcopyfunc->addParamAttr(0, Attribute::NonNull);
      mcopyfunc->addParamAttr(1, Attribute::NonNull);
      mcopyfunc->addDereferenceableParamAttr(0, 24);
      mcopyfunc->addDereferenceableParamAttr(1, 24);

      FunctionType *fty = mcopyfunc->getFunctionType();
      CallInst *mcopyfunc_call =
          CallInst::Create(mcopyfunc, mcopyfunc_arguments_CallArgs, "", for_i);
      AttributeList PAL = mcopyfunc_call->getAttributes();
      PAL =
          PAL.addDereferenceableParamAttr(mcopyfunc_call->getContext(), 0, 24);
      PAL =
          PAL.addDereferenceableParamAttr(mcopyfunc_call->getContext(), 1, 24);
      mcopyfunc_call->setAttributes(PAL);
      mcopyfunc_call->addParamAttr(0, Attribute::NonNull);
      mcopyfunc_call->addParamAttr(1, Attribute::NonNull);

      mcopyfunc_call->setTailCall(false);
      mcopyfunc_call->setDebugLoc(deb);

      std::vector<Value *> get_AES_ctx_ptr_indices;
      get_AES_ctx_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      get_AES_ctx_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      get_AES_ctx_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      Instruction *get_AES_ctx_ptr = GetElementPtrInst::Create(
          ty_struct_ctx, ptr_ctx, get_AES_ctx_ptr_indices, "", for_i);

      std::vector<Value *> get_AES_key_ptr_indices;
      get_AES_key_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      get_AES_key_ptr_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      Instruction *get_AES_key_ptr = GetElementPtrInst::Create(
          array_keyiv, key_alloc, get_AES_key_ptr_indices, "", for_i);

      std::vector<Value *> get_AES_key_iv_indices;
      get_AES_key_iv_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      get_AES_key_iv_indices.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("0"), 10)));
      Instruction *get_AES_iv_ptr = GetElementPtrInst::Create(
          array_keyiv, iv_alloc, get_AES_key_iv_indices, "", for_i);

      std::vector<Value *> aes_init_ctx_iv_arguments;
      aes_init_ctx_iv_arguments.push_back(ptr_ctx);
      aes_init_ctx_iv_arguments.push_back(get_AES_key_ptr);
      aes_init_ctx_iv_arguments.push_back(get_AES_iv_ptr);
      ArrayRef<Value *> aes_init_ctx_iv_CallArgs =
          ArrayRef<Value *>(aes_init_ctx_iv_arguments);

      Function *Func_AES_init_ctx_iv = mod->getFunction("AES_init_ctx_iv");
      CallInst *Func_AES_init_ctx_iv_call = CallInst::Create(
          Func_AES_init_ctx_iv, aes_init_ctx_iv_CallArgs, "", for_i);
      Func_AES_init_ctx_iv_call->setCallingConv(CallingConv::C);
      Func_AES_init_ctx_iv_call->setTailCall(false);
      AttributeList Func_AES_init_ctx_iv_call_PAL;
      Func_AES_init_ctx_iv_call->setAttributes(Func_AES_init_ctx_iv_call_PAL);

      LoadInst *load_i_dec = new LoadInst(
          IntegerType::get(mod->getContext(), 32), ptr_i, "", false, for_i);
      load_i_dec->setAlignment(Align(4)); // 11
      CastInst *casted_i_dec =
          new SExtInst(load_i_dec, IntegerType::get(mod->getContext(), 64), "",
                       for_i); // idxprom15

      std::vector<Value *> get_ret_inst_ptr_indices4;
      get_ret_inst_ptr_indices4.push_back(
          ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));
      get_ret_inst_ptr_indices4.push_back(casted_i_dec);
      Instruction *get_ret_inst_ptr4 = GetElementPtrInst::Create(
          array_out, gvar_ret_inst_list, get_ret_inst_ptr_indices4, "",
          for_i); // arrayidx16

      std::vector<Value *> get_ret_inst_ptr_value_indices4;
      get_ret_inst_ptr_value_indices4.push_back(
          ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));
      get_ret_inst_ptr_value_indices4.push_back(
          ConstantInt::get(mod->getContext(), APInt(64, StringRef("0"), 10)));
      Instruction *get_ret_inst_ptr_value4 = GetElementPtrInst::Create(
          array_in, get_ret_inst_ptr4, get_ret_inst_ptr_value_indices4, "",
          for_i); // arrayidx18

      std::vector<Value *> AES_CTR_xcrypt_buffer_arguments;
      AES_CTR_xcrypt_buffer_arguments.push_back(ptr_ctx);
      AES_CTR_xcrypt_buffer_arguments.push_back(get_ret_inst_ptr_value4);
      AES_CTR_xcrypt_buffer_arguments.push_back(
          ConstantInt::get(mod->getContext(), APInt(32, StringRef("36"), 10)));
      ArrayRef<Value *> AES_CTR_xcrypt_buffer_CallArgs =
          ArrayRef<Value *>(AES_CTR_xcrypt_buffer_arguments);

      Function *Func_AES_CTR_xcrypt_buffer =
          mod->getFunction("AES_CTR_xcrypt_buffer");
      CallInst *Func_AES_CTR_xcrypt_buffer_call =
          CallInst::Create(Func_AES_CTR_xcrypt_buffer,
                           AES_CTR_xcrypt_buffer_CallArgs, "", for_i);
      Func_AES_CTR_xcrypt_buffer_call->setCallingConv(CallingConv::C);
      Func_AES_CTR_xcrypt_buffer_call->setTailCall(false);
      AttributeList Func_AES_CTR_xcrypt_buffer_call_PAL;
      Func_AES_CTR_xcrypt_buffer_call->setAttributes(
          Func_AES_CTR_xcrypt_buffer_call_PAL);
      BranchInst::Create(for_i_add, for_i);

      // for_i_add
      LoadInst *load_i_5 = new LoadInst(IntegerType::get(mod->getContext(), 32),
                                        ptr_i, "", false, for_i_add);
      load_i_5->setAlignment(Align(4));
      BinaryOperator *add_i_1 = BinaryOperator::Create(
          Instruction::Add, load_i_5, const_int_1, "", for_i_add);
      StoreInst *stor_i_2 = new StoreInst(add_i_1, ptr_i, false, for_i_add);
      stor_i_2->setAlignment(Align(4));
      BranchInst::Create(for_i_cond, for_i_add);
      ReturnInst::Create(mod->getContext(), const_int_0, for_i_end);
    }

    int aa = 0;
    if (F.getName().equals("init_modul")) {
      for (auto &BB : F) {
        for (auto &I : BB) {
          aa++;
          if (aa == 1) {
            CallInst *int32_25 = CallInst::Create(Func_deobfus, "", &I);
            int32_25->setCallingConv(CallingConv::C);
            int32_25->setTailCall(false);
            AttributeList int32_25_PAL;
            int32_25->setAttributes(int32_25_PAL);
            int32_25->setDebugLoc(deb);
            InlineFunctionInfo ifi;
            InlineFunction(*int32_25, ifi);
            break;
          }
        }
        break;
      }
    }
    bool found = false;
    AttributeList secure_attrs = F.getAttributes();
    for (auto x : secure_attrs) {
      if (x.hasAttribute("cmse_nonsecure_entry") ||
          x.hasAttribute("cmse_nonsecure_call")) {
        found = true;
      }
    }
    errs() << F.getName() << "\n";
    if (!F.getName().contains("init_module") &&
        !F.getName().contains("__cxx") && !F.getName().contains("_GLOBAL") &&
        !found) {
      errs() << F.getName() << "\n";
      for (auto &BB : F) {
        if (BB.getName().equals("obfuscatedreturn")) {
          GlobalVariable *gvar_ret_inst_list =
              mod->getGlobalVariable("ret_inst_list");
          PointerType *PointerTy_31 =
              PointerType::get(IntegerType::get(mod->getContext(), 8), 0);
          BasicBlock *ret_jmp =
              BasicBlock::Create(mod->getContext(), "ret_jmp", &F, &BB);
          // AllocaInst *ptr_array =
          //   new AllocaInst(array_out, NULL, "ptr_ret_array", jmp_to);
          for (BasicBlock *preds : predecessors(&BB)) {
            preds->getTerminator()->eraseFromParent();
            BranchInst::Create(ret_jmp, preds);
          }
          std::vector<Constant *> const_ptr_14_indices;
          const_ptr_14_indices.push_back(ConstantInt::get(
              mod->getContext(), APInt(64, StringRef("0"), 10)));
          const_ptr_14_indices.push_back(ConstantInt::get(
              mod->getContext(),
              APInt(64, StringRef(std::to_string(num_this_function)), 10)));
          const_ptr_14_indices.push_back(ConstantInt::get(
              mod->getContext(), APInt(64, StringRef("0"), 10)));
          Constant *const_ptr_14 = ConstantExpr::getGetElementPtr(
              array_out, gvar_ret_inst_list, const_ptr_14_indices);
          /*
          std::vector<Value *> ptr_175_indices;
          ptr_175_indices.push_back(const_int_0);
          ptr_175_indices.push_back(ConstantInt::get(
              mod->getContext(),
              APInt(32, StringRef(std::to_string(num_this_function)), 10)));
          errs() << num_this_function << "\n";
          Instruction *ptr_175 = GetElementPtrInst::Create(
              array_out, gvar_ret_inst_list, ptr_175_indices, "", jmp_to);
          std::vector<Value *> ptr_176_indices;
          ptr_176_indices.push_back(const_int_0);
          ptr_176_indices.push_back(const_int_0);
          Instruction *ptr_176 = GetElementPtrInst::Create(
              array_in, ptr_175, ptr_176_indices, "", jmp_to);
          */
        //  IntegerType *IntegerTy_31 =
        //       IntegerType::get(mod->getContext(), 8);

        // PointerType *PointerPointerTy_31 = 
        // PointerType::get(PointerType::get(IntegerType::get(mod->getContext(), 8), 0),0);
        //   StoreInst *void_177 =
        //       new StoreInst(const_ptr_14, ptr_ptr3, false, jmp_to);
        //   void_177->setAlignment(Align(8));
        //   LoadInst *ptr_178 =
        //       new LoadInst(PointerTy_31, ptr_ptr3, "", false, jmp_to);
        //   ptr_178->setAlignment(Align(8));
        //   BranchInst::Create(ret_jmp, jmp_to);

          PHINode *ptr_181 = PHINode::Create(PointerTy_31, 1, "", ret_jmp);
        for (BasicBlock *preds : predecessors(ret_jmp)) {
            ptr_181->addIncoming(const_ptr_14, preds);
          }
          IndirectBrInst *void_182 =
              IndirectBrInst::Create(ptr_181, 1, ret_jmp);
          void_182->addDestination(&BB);
        }
      }
    }

    /*
    Module* mod = F.getParent();
    ArrayType* return_array = ArrayType::get(IntegerType::get(mod->getContext(),
    8), 12); PointerType* return_array_ptr = PointerType::get(return_array, 0);
    PointerType* ret_func_ptr =
    PointerType::get(IntegerType::get(mod->getContext(), 8), 0); ConstantInt*
    const_int_1 = ConstantInt::get(mod->getContext(), APInt(32, StringRef("1"),
    10)); ConstantInt* const_int_0 = ConstantInt::get(mod->getContext(),
    APInt(32, StringRef("0"), 10)); ConstantInt* const_int_20 =
    ConstantInt::get(mod->getContext(), APInt(32, StringRef("12"), 10));
    ConstantInt* const_int32_133 = ConstantInt::get(mod->getContext(), APInt(32,
    StringRef("133"), 10)); AllocaInst* ptr_ret_array; AllocaInst* ptr_this_ret;
    AllocaInst* ret_array_ptr;
    AllocaInst* ptr_i;
    std::vector<Instruction *> instructions;
    std::vector<BasicBlock *> RetBlocks;
    bool inserted = false;
    bool splitted = false;
    for (auto &BB : F) {
        for (auto &I : BB) {
            if(!inserted) {
                ptr_ret_array = new AllocaInst(return_array, NULL, "ret_ptr",
    &I); ptr_ret_array->setAlignment(Align(1)); ptr_this_ret = new
    AllocaInst(ret_func_ptr, NULL,  "ptr", &I); ret_array_ptr = new
    AllocaInst(ret_func_ptr, NULL, "ptr2", &I); ptr_i = new
    AllocaInst(IntegerType::get(mod->getContext(), 32), NULL,  "i", &I);

                inserted=true;
                IndirectBrInst *a;

            }
            if (I.getOpcode() == Instruction::Ret) {
                instructions.push_back(&I);
            }
        }
    }

    for (auto &I : instructions) {
        BasicBlock *BB = I->getParent();
        // One Instruction Basic Block has only one ret instructions
        if (!BB->size() < 2)
        {
            BasicBlock *retblock = BB->splitBasicBlock(I->getIterator(),
    BB->getName() + ".RetBlock"); RetBlocks.push_back(retblock); } else {
            RetBlocks.push_back(BB);
        }

    }

    for (auto &BB : RetBlocks) {
        Constant* retBlockAddress = BlockAddress::get(BB);
        Module* M = F.getParent();

        for (auto curFref = M->getFunctionList().begin(),
                endFref = M->getFunctionList().end();
                curFref != endFref; ++curFref) {
            for (auto& B: curFref->getBasicBlockList()) {
                StoreInst* asdf = new StoreInst(retBlockAddress, ptr_this_ret,
    false, &B); asdf->setAlignment(Align(4)); break;
            }

        }
        BasicBlock* decrypt_start = BasicBlock::Create(mod->getContext(),
    "dec_start", &F, BB); for (BasicBlock* preds : predecessors(BB)) {
            preds->getTerminator()->eraseFromParent();
            BranchInst::Create(decrypt_start, preds);
        }


        std::vector<Value*> ptr_to_retarray_indices;
        ptr_to_retarray_indices.push_back(const_int_0);
        ptr_to_retarray_indices.push_back(const_int_0);
        GetElementPtrInst* ptr_to_retarray =
    GetElementPtrInst::Create(return_array, ptr_ret_array,
    ptr_to_retarray_indices, "arrayidx", decrypt_start);
        ptr_to_retarray->setIsInBounds(true);
        StoreInst* store_to_ret_ptr = new StoreInst(ptr_to_retarray,
    ret_array_ptr, false, decrypt_start);

        store_to_ret_ptr->setAlignment(Align(4));

        StoreInst* void_17 = new StoreInst(retBlockAddress, ptr_this_ret, false,
    decrypt_start);

        ptr_this_ret->setAlignment(Align(4));
        ret_array_ptr->setAlignment(Align(4));
        ptr_i->setAlignment(Align(4));
        void_17->setAlignment(Align(4));



        StoreInst* store_i_0 = new StoreInst(const_int_0, ptr_i, false,
    decrypt_start); store_i_0->setAlignment(Align(4));



        BasicBlock* decrypt_cond = BasicBlock::Create(mod->getContext(),
    "dec_cond", &F, BB);

        BranchInst::Create(decrypt_cond, decrypt_start);

        LoadInst* ldr_i_data = new LoadInst(ptr_i, "", false, decrypt_cond);
        ldr_i_data->setAlignment(Align(4));
        ICmpInst* cmp_i_with_20 = new ICmpInst(*decrypt_cond,
    ICmpInst::ICMP_SLT, ldr_i_data, const_int_20, "cmp");

        BasicBlock* decrypt_ing = BasicBlock::Create(mod->getContext(),
    "dec_ing", &F, BB); BasicBlock* decrypt_add =
    BasicBlock::Create(mod->getContext(), "dec_add", &F, BB); BasicBlock*
    decrypt_end = BasicBlock::Create(mod->getContext(), "dec_end", &F, BB);
        BranchInst::Create(decrypt_ing, decrypt_end, cmp_i_with_20,
    decrypt_cond);

        LoadInst* ldr_i_data_2 = new LoadInst(ptr_i, "", false, decrypt_ing);
        ldr_i_data_2->setAlignment(Align(4));
        LoadInst* ldr_ptr_this_ret = new LoadInst(ptr_this_ret, "", false,
    decrypt_ing); ldr_ptr_this_ret->setAlignment(Align(4));
        GetElementPtrInst* get_func_ptr_idx =
    GetElementPtrInst::Create(cast<PointerType>(ldr_ptr_this_ret->getType()->getScalarType())->getElementType(),
    ldr_ptr_this_ret, ldr_i_data_2, "arrayidx1", decrypt_ing);
        get_func_ptr_idx->setIsInBounds(true);


        LoadInst* ldr_func_ptr_idx = new LoadInst(get_func_ptr_idx, "", false,
    decrypt_ing); ldr_func_ptr_idx->setAlignment(Align(1));

        LoadInst* ldr_i_data_3 = new LoadInst(ptr_i, "", false, decrypt_ing);
        ldr_i_data_3->setAlignment(Align(4));

        std::vector<Value*> ptr_retn_array_indices;
        ptr_retn_array_indices.push_back(const_int_0);
        ptr_retn_array_indices.push_back(ldr_i_data_3);
        GetElementPtrInst* get_retn_array_data_idx =
    GetElementPtrInst::Create(return_array, ptr_ret_array,
    ptr_retn_array_indices, "arrayidx2", decrypt_ing);
        get_retn_array_data_idx->setIsInBounds(true);
        StoreInst* str_retn_array_data_idx = new StoreInst(ldr_func_ptr_idx,
    get_retn_array_data_idx, false, decrypt_ing);
        str_retn_array_data_idx->setAlignment(Align(1));

        LoadInst* ldr_i_data_4 = new LoadInst(ptr_i, "", false, decrypt_ing);
        ldr_i_data_4->setAlignment(Align(4));

        std::vector<Value*> ptr_retn_array_indices2;
        ptr_retn_array_indices2.push_back(const_int_0);
        ptr_retn_array_indices2.push_back(ldr_i_data_4);
        GetElementPtrInst* get_retn_array_data_idx2 =
    GetElementPtrInst::Create(return_array, ptr_ret_array,
    ptr_retn_array_indices2, "arrayidx3", decrypt_ing);
        get_retn_array_data_idx2->setIsInBounds(true);
        LoadInst* ldr_retn_array_data_idx2 = new
    LoadInst(get_retn_array_data_idx2, "", false, decrypt_ing);
        ldr_retn_array_data_idx2->setAlignment(Align(1));

        CastInst* cast_retn_array_data_idx2 = new
    ZExtInst(ldr_retn_array_data_idx2, IntegerType::get(mod->getContext(), 32),
    "conv", decrypt_ing); BinaryOperator* xor_retn_array_data_idx2 =
    BinaryOperator::Create(Instruction::Xor, cast_retn_array_data_idx2,
    const_int32_133, "xor", decrypt_ing);

        CastInst* trun_retn_array_data_idx2 = new
    TruncInst(xor_retn_array_data_idx2, IntegerType::get(mod->getContext(), 8),
    "conv4", decrypt_ing);


        LoadInst* ldr_i_data_5 = new LoadInst(ptr_i, "", false, decrypt_ing);
        ldr_i_data_5->setAlignment(Align(4));

        std::vector<Value*> ptr_retn_array_indices4;
        ptr_retn_array_indices4.push_back(const_int_0);
        ptr_retn_array_indices4.push_back(ldr_i_data_5);
        GetElementPtrInst* get_retn_array_data_idx4 =
    GetElementPtrInst::Create(return_array, ptr_ret_array,
    ptr_retn_array_indices4, "arrayidx5", decrypt_ing);
        get_retn_array_data_idx4->setIsInBounds(true);
        StoreInst* str_retn_array_data_idx4 = new
    StoreInst(trun_retn_array_data_idx2, get_retn_array_data_idx4, false,
    decrypt_ing); str_retn_array_data_idx4->setAlignment(Align(1));


        BranchInst::Create(decrypt_add, decrypt_ing);

        LoadInst* ldr_i_data_6 = new LoadInst(ptr_i, "", false, decrypt_add);
        ldr_i_data_6->setAlignment(Align(4));
        BinaryOperator* add_i_data_4 = BinaryOperator::Create(Instruction::Add,
    ldr_i_data_6, const_int_1, "", decrypt_add); StoreInst* str_i_data_4 = new
    StoreInst(add_i_data_4, ptr_i, false, decrypt_add);
        str_i_data_4->setAlignment(Align(4));
        BranchInst::Create(decrypt_cond, decrypt_add);



        LoadInst* ldr_ret_array = new LoadInst(ret_array_ptr, "", false,
    decrypt_end); ldr_ret_array->setAlignment(Align(4));

        BasicBlock* dec_jmp = BasicBlock::Create(mod->getContext(), "dec_jmp",
    &F, BB); BranchInst::Create(dec_jmp, decrypt_end);

        PHINode* ptr_40 = PHINode::Create(ret_func_ptr, 1, "", dec_jmp);
        ptr_40->addIncoming(ldr_ret_array, decrypt_end);
        IndirectBrInst *void_41 = IndirectBrInst::Create(ldr_ret_array, 1,
    dec_jmp); void_41->addDestination(BB); errs().write_escaped(F.getName()) <<
    "   " <<  F.getParent()->getName() <<  '\n';
    }
    */
    return true;
  }

}; // end of struct Hello
} // end of anonymous namespace

char ReturnObfuscation::ID = 0;

static RegisterPass<ReturnObfuscation> X("rof", "Hello World Pass",
                                         false /* Only looks at CFG */,
                                         false /* Analysis Pass */);
