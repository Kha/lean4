// Lean compiler output
// Module: Lean.Compiler.ConstFolding
// Imports: Init Lean.Expr Lean.Compiler.Util
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Compiler_unFoldFns___closed__5;
lean_object* l_Lean_Compiler_unFoldFns___closed__3;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__5;
lean_object* l_Lean_Compiler_mkNatLe(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__14;
extern lean_object* l_Nat_instDivNat___closed__1;
lean_object* l_Lean_Compiler_foldNatBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__15;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__18;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__23;
uint8_t l_List_foldr___at_Lean_Compiler_isToNat___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_NumScalarTypeInfo_id___default(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_boolFoldFns___closed__3;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__13;
lean_object* l_Lean_Compiler_foldStrictAnd_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__25;
lean_object* l_Lean_Compiler_foldStrictAnd_match__1(lean_object*);
lean_object* l_Lean_Compiler_uintFoldToNatFns___closed__1;
lean_object* l_Lean_Compiler_foldUIntMod___closed__1;
lean_object* l_Lean_Compiler_natFoldFns___closed__5;
lean_object* l_Lean_Compiler_foldCharOfNat___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__30;
lean_object* l_Lean_Compiler_NumScalarTypeInfo_size___default___boxed(lean_object*);
lean_object* l_Lean_Compiler_foldCharOfNat___closed__1;
lean_object* l_Lean_Compiler_foldUIntSub___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__15;
extern lean_object* l_UInt64_size___closed__1;
lean_object* l_Lean_Compiler_foldCharOfNat___closed__2;
lean_object* l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default(lean_object*);
extern lean_object* l_System_Platform_numBits;
lean_object* l_Lean_Compiler_foldNatPow___boxed(lean_object*);
lean_object* l_Lean_Compiler_foldUIntMod___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__14;
lean_object* l_Lean_Compiler_boolFoldFns___closed__7;
lean_object* l_Lean_Compiler_natFoldFns___closed__28;
lean_object* l_Lean_Compiler_natFoldFns___closed__18;
lean_object* l_Lean_Compiler_foldNatDiv___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__6;
lean_object* l_Lean_Compiler_foldStrictAnd(uint8_t);
lean_object* l_Lean_Compiler_getBoolLit___closed__2;
lean_object* l_Lean_Compiler_preUIntBinFoldFns;
lean_object* l_Lean_Compiler_foldStrictAnd___boxed(lean_object*);
lean_object* l_Lean_Compiler_natFoldFns;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__25;
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_boolFoldFns___closed__5;
lean_object* l_Lean_Compiler_foldUIntSub(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldToNat___rarg(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__19;
extern lean_object* l_instReprBool___closed__1;
lean_object* l_Lean_Compiler_foldNatDecLe___closed__2;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__9;
lean_object* l_Lean_Compiler_foldUIntSub___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_USize_size___closed__1;
lean_object* l_Lean_Compiler_NumScalarTypeInfo_size___default(lean_object*);
lean_object* l_Lean_Compiler_foldUIntSub___closed__1;
lean_object* l_Lean_Compiler_foldNatPow___rarg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatMod(uint8_t);
lean_object* l_Lean_Compiler_getNumLit_match__1(lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__27;
lean_object* l_Lean_Compiler_getNumLit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__9;
lean_object* l_Lean_Compiler_natFoldFns___closed__40;
lean_object* l_Lean_Compiler_natFoldFns___closed__4;
lean_object* l_Lean_Compiler_numScalarTypes___closed__20;
lean_object* l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1;
lean_object* l_Lean_Compiler_foldUIntAdd___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__1;
lean_object* l_Lean_Compiler_natFoldFns___closed__31;
lean_object* l_Lean_Compiler_foldNatMul___boxed(lean_object*);
lean_object* l_Lean_Compiler_binFoldFns___closed__2;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__22;
lean_object* l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
lean_object* l_Lean_Compiler_uintFoldToNatFns;
lean_object* l_Lean_Compiler_foldNatDecLe___closed__1;
extern lean_object* l_Lean_instQuoteBool___closed__1;
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_Compiler_foldNatAdd___boxed(lean_object*);
lean_object* l_Lean_Compiler_foldNatDecLe___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatDiv(uint8_t);
extern lean_object* l_Lean_levelZero;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__19;
lean_object* l_Lean_Compiler_mkUInt32Lit(lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__17;
lean_object* l_Lean_Compiler_natFoldFns___closed__37;
extern lean_object* l_Lean_Compiler_neutralExpr;
lean_object* l_Lean_Compiler_numScalarTypes___closed__4;
lean_object* l_Lean_Compiler_natFoldFns___closed__16;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInfoFromVal_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_binFoldFns;
lean_object* l_Lean_Compiler_mkNatLe___closed__2;
lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldStrictOr___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__7;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__21;
lean_object* l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__8;
lean_object* l_Lean_Compiler_binFoldFns___closed__1;
lean_object* l_Lean_Compiler_mkNatEq___closed__3;
lean_object* l_Lean_Compiler_foldUIntDiv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__21;
lean_object* l_Lean_Compiler_natFoldFns___closed__38;
lean_object* l_Lean_Compiler_foldNatDecEq(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldUIntDiv___closed__1;
lean_object* l_Lean_Compiler_toDecidableExpr___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_fold_un_op(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_toDecidableExpr___closed__1;
lean_object* l_Lean_Compiler_boolFoldFns___closed__6;
lean_object* l_Lean_Compiler_unFoldFns___closed__6;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkNatLe___closed__3;
lean_object* l_Lean_Compiler_foldUnOp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkNatEq___closed__1;
lean_object* l_Lean_Compiler_foldNatMul(uint8_t);
lean_object* l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatDecLt(uint8_t, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_isOfNat(lean_object*);
lean_object* l_Lean_Compiler_foldStrictOr___boxed(lean_object*);
lean_object* l_Lean_Compiler_mkNatLt___closed__5;
lean_object* l_Lean_Compiler_foldNatSucc___boxed(lean_object*);
lean_object* l_Lean_Compiler_mkNatLe___closed__5;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__8;
lean_object* l_Lean_Compiler_foldUIntDiv___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__17;
lean_object* l_Lean_Compiler_numScalarTypes___closed__3;
lean_object* l_Lean_Compiler_unFoldFns___closed__4;
lean_object* l_Lean_Compiler_numScalarTypes___closed__5;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__4;
lean_object* l_Lean_Compiler_unFoldFns___closed__9;
lean_object* l_Lean_Compiler_numScalarTypes___closed__18;
lean_object* l_Lean_Compiler_toDecidableExpr_match__1(lean_object*);
uint8_t l_UInt32_decLt(uint32_t, uint32_t);
lean_object* l_Lean_Compiler_numScalarTypes___closed__15;
lean_object* l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__14;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__12;
extern lean_object* l_instReprBool___closed__3;
lean_object* l_Lean_Compiler_boolFoldFns___closed__8;
lean_object* l_Lean_Compiler_getBoolLit_match__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldUIntMod___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getInfoFromFn(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkNatEq___closed__4;
lean_object* l_Lean_Compiler_unFoldFns___closed__8;
lean_object* l_Lean_Compiler_natFoldFns___closed__12;
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_Compiler_findUnFoldFn(lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__22;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__2;
lean_object* l_Lean_Compiler_natFoldFns___closed__20;
lean_object* l_Lean_Compiler_unFoldFns___closed__1;
lean_object* l_Lean_Compiler_natFoldFns___closed__26;
lean_object* lean_fold_bin_op(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__32;
lean_object* l_Lean_Compiler_natFoldFns___closed__10;
lean_object* l_Lean_Compiler_isOfNat___boxed(lean_object*);
lean_object* l_Lean_Compiler_mkNatLt___closed__7;
lean_object* l_Lean_Compiler_getBoolLit(lean_object*);
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__1;
lean_object* l_Lean_Compiler_mkLcProof(lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__9;
lean_object* l_Lean_Compiler_mkUIntTypeName(lean_object*);
extern lean_object* l_instMulNat___closed__1;
lean_object* l_Lean_Compiler_getInfoFromFn_match__1(lean_object*);
lean_object* l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_uintBinFoldFns_match__1___rarg(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_isCharLit___closed__3;
lean_object* l_Lean_Compiler_unFoldFns___closed__2;
lean_object* l_Lean_Compiler_boolFoldFns___closed__2;
lean_object* l_Lean_Compiler_getInfoFromVal_match__1(lean_object*);
lean_object* l_Lean_Compiler_boolFoldFns___closed__4;
lean_object* l_Lean_Compiler_numScalarTypes___closed__26;
lean_object* l_Lean_Compiler_mkUIntTypeName___closed__1;
extern lean_object* l_Lean_Literal_type___closed__2;
lean_object* l_Lean_Compiler_mkUIntLit___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatPow(uint8_t);
lean_object* l_Lean_Compiler_numScalarTypes___closed__12;
lean_object* l_Lean_Compiler_foldCharOfNat(uint8_t, lean_object*);
lean_object* l_Lean_Compiler_foldStrictAnd___rarg(lean_object*, lean_object*);
lean_object* l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatMod___boxed(lean_object*);
lean_object* l_Lean_Compiler_mkNatEq___closed__5;
lean_object* l_Lean_Compiler_boolFoldFns___closed__9;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_6055____closed__7;
lean_object* l_Lean_Compiler_foldUIntMul___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__2;
lean_object* l_Lean_Compiler_getInfoFromFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldUIntMul___closed__1;
lean_object* l_Lean_Compiler_foldBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatDecLe(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__11;
lean_object* l_Lean_Compiler_natFoldFns___closed__6;
lean_object* l_Lean_Compiler_foldUIntMod(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_toDecidableExpr_match__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldToNat___boxed(lean_object*);
lean_object* l_Lean_Compiler_boolFoldFns___closed__1;
lean_object* l_Lean_Compiler_foldNatBinPred(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkNatLt___closed__2;
lean_object* l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_unFoldFns___closed__7;
lean_object* l_Lean_Compiler_foldNatDiv___boxed(lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__34;
lean_object* l_Lean_Compiler_unFoldFns;
lean_object* l_Lean_Compiler_uintBinFoldFns;
lean_object* l_Lean_Compiler_natFoldFns___closed__11;
lean_object* l_Lean_Compiler_natFoldFns___closed__22;
lean_object* l_Lean_Compiler_mkNatLt___closed__3;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__7;
lean_object* l_Lean_Compiler_numScalarTypes___closed__23;
lean_object* l_Lean_Compiler_mkNatEq___closed__2;
lean_object* l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatBinOp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__3;
lean_object* l_Lean_Compiler_getBoolLit_match__1(lean_object*);
lean_object* l_Lean_Compiler_foldNatMod___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatSucc___rarg(lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__21;
lean_object* l_Lean_Compiler_natFoldFns___closed__29;
lean_object* l_Lean_Compiler_natFoldFns___closed__33;
lean_object* l_Lean_Compiler_foldUIntDiv(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_isToNat___boxed(lean_object*);
lean_object* l_Nat_decLe___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldUIntAdd___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_uintBinFoldFns___closed__1;
lean_object* l_Lean_Compiler_findBinFoldFn(lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__13;
lean_object* l_Lean_Compiler_foldUIntAdd___closed__1;
lean_object* l_Lean_Compiler_mkNatLt(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkUIntLit(lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Compiler_uintBinFoldFns___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldBinUInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__24;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkNatLe___closed__1;
lean_object* l_Lean_Compiler_numScalarTypes___closed__2;
lean_object* l_Lean_Compiler_mkNatLe___closed__4;
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Lean_Compiler_foldUIntDiv___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_toDecidableExpr_match__1___rarg(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_mkNatLt___closed__6;
lean_object* l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default(lean_object*);
lean_object* l_Lean_Compiler_foldNatAdd(uint8_t);
lean_object* l_Lean_Compiler_natFoldFns___closed__24;
lean_object* l_Lean_Compiler_foldStrictOr(uint8_t);
lean_object* l_Lean_Compiler_mkNatLt___closed__4;
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__36;
lean_object* l_Lean_Compiler_numScalarTypes___closed__10;
lean_object* l_Lean_Compiler_natFoldFns___closed__35;
lean_object* l_Lean_Compiler_findBinFoldFn___boxed(lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__17;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__3;
lean_object* l_Lean_Compiler_natPowThreshold;
lean_object* l_Lean_Compiler_numScalarTypes___closed__24;
lean_object* l_Lean_Compiler_getInfoFromFn_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatDecLt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_map___at_Lean_Compiler_uintBinFoldFns___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldUIntSub___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_isToNat(lean_object*);
lean_object* l_Lean_Compiler_foldNatMul___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldToNat(uint8_t);
lean_object* l_Lean_Compiler_mkNatEq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldUIntMod___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Position_lt___closed__1;
lean_object* l_Lean_Compiler_getInfoFromVal(lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__16;
lean_object* l_Lean_Compiler_foldNatSucc(uint8_t);
lean_object* l_Lean_Compiler_toDecidableExpr(uint8_t, lean_object*, uint8_t);
uint8_t l_List_foldr___at_Lean_Compiler_isOfNat___spec__1(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_foldNatAdd___rarg(lean_object*, lean_object*);
extern lean_object* l_instAddNat___closed__1;
lean_object* l_Lean_Compiler_mkUInt32Lit___boxed(lean_object*);
lean_object* l_List_foldr___at_Lean_Compiler_isToNat___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatDecEq___closed__1;
lean_object* l_Lean_Compiler_foldBinUInt(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldUIntAdd(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldBinOp_match__1(lean_object*);
lean_object* l_List_foldr___at_Lean_Compiler_isOfNat___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__39;
lean_object* lean_nat_mod(lean_object*, lean_object*);
extern lean_object* l_myMacro____x40_Init_Notation___hyg_7609____closed__4;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__7;
lean_object* l_Lean_Compiler_natFoldFns___closed__1;
lean_object* l_Lean_Compiler_numScalarTypes___closed__19;
lean_object* l_Lean_Compiler_getInfoFromVal___boxed(lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__23;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__16;
lean_object* l_Lean_Compiler_foldUIntMul___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldBinOp_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_numScalarTypes___closed__11;
extern lean_object* l_Lean_levelOne;
lean_object* l_Lean_Compiler_foldUIntMul(uint8_t, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_isCharLit___closed__4;
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__6;
lean_object* lean_get_num_lit(lean_object*);
lean_object* l_Lean_Compiler_foldNatDecLt___closed__1;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_boolFoldFns;
lean_object* l_Lean_Compiler_getBoolLit___closed__1;
lean_object* l_Lean_Compiler_findUnFoldFn___boxed(lean_object*);
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__10;
lean_object* l_Lean_Compiler_natFoldFns___closed__25;
lean_object* l_Lean_Compiler_getBoolLit___boxed(lean_object*);
lean_object* l_Lean_Compiler_preUIntBinFoldFns___closed__20;
lean_object* l_Lean_Compiler_mkNatLt___closed__1;
extern lean_object* l_Lean_Position_lt___closed__2;
extern lean_object* l_myMacro____x40_Init_Notation___hyg_6577____closed__7;
lean_object* l_Lean_Compiler_natFoldFns___closed__8;
lean_object* l_Lean_Compiler_foldUIntAdd___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_natFoldFns___closed__13;
lean_object* l_Lean_Compiler_foldUIntMul___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_Nat_instModNat___closed__1;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_foldNatDecEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_boolFoldFns___closed__10;
lean_object* l_Lean_Compiler_uintBinFoldFns_match__1(lean_object*);
lean_object* l_Lean_Compiler_toDecidableExpr___closed__2;
static lean_object* _init_l_Lean_Compiler_mkUIntTypeName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("UInt");
return x_1;
}
}
lean_object* l_Lean_Compiler_mkUIntTypeName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_Compiler_mkUIntTypeName___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_name_mk_string(x_5, x_4);
return x_6;
}
}
lean_object* l_Lean_Compiler_NumScalarTypeInfo_id___default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_NumScalarTypeInfo_ofNatFn___default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Expr_isCharLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toNat");
return x_1;
}
}
lean_object* l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_NumScalarTypeInfo_size___default(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Compiler_NumScalarTypeInfo_size___default___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_NumScalarTypeInfo_size___default(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__1;
x_2 = l_Lean_Expr_isCharLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__1;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_Compiler_numScalarTypes___closed__1;
x_3 = l_Lean_Compiler_numScalarTypes___closed__2;
x_4 = l_Lean_Compiler_numScalarTypes___closed__3;
x_5 = lean_unsigned_to_nat(256u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__5;
x_2 = l_Lean_Expr_isCharLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__5;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(16u);
x_2 = l_Lean_Compiler_numScalarTypes___closed__5;
x_3 = l_Lean_Compiler_numScalarTypes___closed__6;
x_4 = l_Lean_Compiler_numScalarTypes___closed__7;
x_5 = lean_unsigned_to_nat(65536u);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__9;
x_2 = l_Lean_Expr_isCharLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__9;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = l_Lean_Compiler_numScalarTypes___closed__9;
x_3 = l_Lean_Compiler_numScalarTypes___closed__10;
x_4 = l_Lean_Compiler_numScalarTypes___closed__11;
x_5 = lean_cstr_to_nat("4294967296");
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__13;
x_2 = l_Lean_Expr_isCharLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__13;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_unsigned_to_nat(64u);
x_2 = l_Lean_Compiler_numScalarTypes___closed__13;
x_3 = l_Lean_Compiler_numScalarTypes___closed__14;
x_4 = l_Lean_Compiler_numScalarTypes___closed__15;
x_5 = l_UInt64_size___closed__1;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("USize");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__18;
x_2 = l_Lean_Expr_isCharLit___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__18;
x_2 = l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_System_Platform_numBits;
x_2 = l_Lean_Compiler_numScalarTypes___closed__18;
x_3 = l_Lean_Compiler_numScalarTypes___closed__19;
x_4 = l_Lean_Compiler_numScalarTypes___closed__20;
x_5 = l_USize_size___closed__1;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__16;
x_2 = l_Lean_Compiler_numScalarTypes___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__12;
x_2 = l_Lean_Compiler_numScalarTypes___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__8;
x_2 = l_Lean_Compiler_numScalarTypes___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__4;
x_2 = l_Lean_Compiler_numScalarTypes___closed__25;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_numScalarTypes___closed__26;
return x_1;
}
}
uint8_t l_List_foldr___at_Lean_Compiler_isOfNat___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___at_Lean_Compiler_isOfNat___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_name_eq(x_7, x_1);
if (x_8 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
uint8_t l_Lean_Compiler_isOfNat(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint8_t x_4; 
x_2 = 0;
x_3 = l_Lean_Compiler_numScalarTypes;
x_4 = l_List_foldr___at_Lean_Compiler_isOfNat___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_foldr___at_Lean_Compiler_isOfNat___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at_Lean_Compiler_isOfNat___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Compiler_isOfNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isOfNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_List_foldr___at_Lean_Compiler_isToNat___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = l_List_foldr___at_Lean_Compiler_isToNat___spec__1(x_1, x_2, x_5);
x_7 = lean_ctor_get(x_4, 3);
x_8 = lean_name_eq(x_7, x_1);
if (x_8 == 0)
{
return x_6;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
uint8_t l_Lean_Compiler_isToNat(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; uint8_t x_4; 
x_2 = 0;
x_3 = l_Lean_Compiler_numScalarTypes;
x_4 = l_List_foldr___at_Lean_Compiler_isToNat___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_List_foldr___at_Lean_Compiler_isToNat___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_List_foldr___at_Lean_Compiler_isToNat___spec__1(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
lean_object* l_Lean_Compiler_isToNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isToNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_getInfoFromFn_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Compiler_getInfoFromFn_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_getInfoFromFn_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_getInfoFromFn(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_name_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
}
}
}
lean_object* l_Lean_Compiler_getInfoFromFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getInfoFromFn(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Compiler_getInfoFromVal_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 4)
{
lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
lean_dec(x_4);
x_10 = lean_box_uint64(x_9);
x_11 = lean_box_uint64(x_6);
x_12 = lean_apply_5(x_2, x_7, x_8, x_10, x_5, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_4);
lean_dec(x_2);
x_13 = lean_apply_1(x_3, x_1);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_2);
x_14 = lean_apply_1(x_3, x_1);
return x_14;
}
}
}
lean_object* l_Lean_Compiler_getInfoFromVal_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_getInfoFromVal_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_getInfoFromVal(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Compiler_numScalarTypes;
x_5 = l_Lean_Compiler_getInfoFromFn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
lean_object* l_Lean_Compiler_getInfoFromVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_getInfoFromVal(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_getNumLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; uint64_t x_7; lean_object* x_8; lean_object* x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_dec(x_5);
x_11 = lean_box_uint64(x_10);
x_12 = lean_box_uint64(x_7);
x_13 = lean_apply_5(x_3, x_8, x_9, x_11, x_6, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
x_14 = lean_apply_1(x_4, x_1);
return x_14;
}
}
case 9:
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint64_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
x_16 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box_uint64(x_16);
x_19 = lean_apply_2(x_2, x_17, x_18);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_15);
lean_dec(x_2);
x_20 = lean_apply_1(x_4, x_1);
return x_20;
}
}
default: 
{
lean_object* x_21; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_apply_1(x_4, x_1);
return x_21;
}
}
}
}
lean_object* l_Lean_Compiler_getNumLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_getNumLit_match__1___rarg), 4, 0);
return x_2;
}
}
lean_object* lean_get_num_lit(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = 0;
x_6 = l_Lean_Compiler_numScalarTypes;
x_7 = l_List_foldr___at_Lean_Compiler_isOfNat___spec__1(x_4, x_5, x_6);
lean_dec(x_4);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_box(0);
return x_8;
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
}
case 9:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_box(0);
return x_14;
}
}
default: 
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_box(0);
return x_15;
}
}
}
}
lean_object* l_Lean_Compiler_mkUIntLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l_Lean_mkConst(x_3, x_4);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_nat_mod(x_2, x_6);
lean_dec(x_6);
x_8 = l_Lean_mkNatLit(x_7);
x_9 = l_Lean_mkApp(x_5, x_8);
return x_9;
}
}
lean_object* l_Lean_Compiler_mkUIntLit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_mkUIntLit(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_mkUInt32Lit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_numScalarTypes___closed__12;
x_3 = l_Lean_Compiler_mkUIntLit(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_Compiler_mkUInt32Lit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_mkUInt32Lit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldBinUInt(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_get_num_lit(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_get_num_lit(x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_getInfoFromVal(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_box(x_2);
lean_inc(x_14);
x_16 = lean_apply_4(x_1, x_14, x_15, x_7, x_10);
x_17 = l_Lean_Compiler_mkUIntLit(x_14, x_16);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(x_2);
lean_inc(x_18);
x_20 = lean_apply_4(x_1, x_18, x_19, x_7, x_10);
x_21 = l_Lean_Compiler_mkUIntLit(x_18, x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
lean_object* l_Lean_Compiler_foldBinUInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldBinUInt(x_1, x_5, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldUIntAdd___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_add(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntAdd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntAdd___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldUIntAdd(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntAdd___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntAdd___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntAdd___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldUIntAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntAdd(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntMul___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_mul(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntMul___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMul___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldUIntMul(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntMul___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntMul___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntMul___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldUIntMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntMul(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntDiv___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_div(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntDiv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntDiv___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldUIntDiv(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntDiv___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntDiv___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntDiv___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldUIntDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntDiv(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntMod___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_mod(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntMod___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMod___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldUIntMod(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntMod___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntMod___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntMod___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldUIntMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntMod(x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntSub___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_foldUIntSub___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntSub___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldUIntSub(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_foldUIntSub___closed__1;
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_Compiler_foldUIntSub___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntSub___lambda__1(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldUIntSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntSub(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("add");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntAdd___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__2;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mul");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMul___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__6;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("div");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntDiv___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__10;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mod");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMod___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__14;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("sub");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntSub___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__18;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__19;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__20;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__16;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__21;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__12;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__22;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__8;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__23;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__4;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__24;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_preUIntBinFoldFns___closed__25;
return x_1;
}
}
lean_object* l_Lean_Compiler_uintBinFoldFns_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Compiler_uintBinFoldFns_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_uintBinFoldFns_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_List_map___at_Lean_Compiler_uintBinFoldFns___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = l_List_map___at_Lean_Compiler_uintBinFoldFns___spec__1(x_1, x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l_Lean_Name_append(x_10, x_9);
lean_ctor_set(x_5, 0, x_11);
lean_ctor_set(x_2, 1, x_7);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Lean_Name_append(x_14, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_16);
return x_2;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_2);
x_19 = l_List_map___at_Lean_Compiler_uintBinFoldFns___spec__1(x_1, x_18);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_22 = x_17;
} else {
 lean_dec_ref(x_17);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_1, 1);
x_24 = l_Lean_Name_append(x_23, x_20);
if (lean_is_scalar(x_22)) {
 x_25 = lean_alloc_ctor(0, 2, 0);
} else {
 x_25 = x_22;
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_19);
return x_26;
}
}
}
}
lean_object* l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_Compiler_preUIntBinFoldFns;
x_6 = l_List_map___at_Lean_Compiler_uintBinFoldFns___spec__1(x_3, x_5);
x_7 = l_List_append___rarg(x_1, x_6);
x_1 = x_7;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Compiler_uintBinFoldFns___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes;
x_3 = l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_uintBinFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_uintBinFoldFns___closed__1;
return x_1;
}
}
lean_object* l_List_map___at_Lean_Compiler_uintBinFoldFns___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_map___at_Lean_Compiler_uintBinFoldFns___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_foldl___at_Lean_Compiler_uintBinFoldFns___spec__2(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_foldNatBinOp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_get_num_lit(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = l_Lean_mkNatLit(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_apply_2(x_1, x_6, x_13);
x_15 = l_Lean_mkNatLit(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
lean_object* l_Lean_Compiler_foldNatAdd___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_instAddNat___closed__1;
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Compiler_foldNatAdd(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatAdd___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldNatAdd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatAdd(x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_foldNatMul___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_instMulNat___closed__1;
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Compiler_foldNatMul(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMul___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldNatMul___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatMul(x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_foldNatDiv___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Nat_instDivNat___closed__1;
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Compiler_foldNatDiv(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDiv___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldNatDiv___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatDiv(x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_foldNatMod___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Nat_instModNat___closed__1;
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_Compiler_foldNatMod(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMod___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldNatMod___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatMod(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natPowThreshold() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(256u);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldNatPow___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_num_lit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_Compiler_natPowThreshold;
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_6);
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_nat_pow(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_14 = l_Lean_mkNatLit(x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l_Lean_Compiler_natPowThreshold;
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_5);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_nat_pow(x_5, x_15);
lean_dec(x_15);
lean_dec(x_5);
x_20 = l_Lean_mkNatLit(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
}
lean_object* l_Lean_Compiler_foldNatPow(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatPow___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldNatPow___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatPow(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelOne;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_7609____closed__4;
x_2 = l_Lean_Compiler_mkNatEq___closed__1;
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Literal_type___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatEq___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatEq___closed__4;
x_2 = l_Lean_Compiler_mkNatEq___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_mkNatEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_mkNatEq___closed__5;
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = l_Lean_Compiler_mkNatEq___closed__2;
x_7 = l_Lean_mkAppN(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_levelZero;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_6577____closed__7;
x_2 = l_Lean_Compiler_mkNatLt___closed__1;
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("less");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_mkNatLt___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkNatLt___closed__4;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_2 = l_Lean_Compiler_mkNatEq___closed__3;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLt___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLt___closed__6;
x_2 = l_Lean_Compiler_mkNatLt___closed__5;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_mkNatLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_mkNatLt___closed__7;
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = l_Lean_Compiler_mkNatLt___closed__2;
x_7 = l_Lean_mkAppN(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_myMacro____x40_Init_Notation___hyg_6055____closed__7;
x_2 = l_Lean_Compiler_mkNatLt___closed__1;
x_3 = l_Lean_mkConst(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("lessEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_mkNatLe___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_mkNatLe___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_mkNatLe___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_mkNatLt___closed__6;
x_2 = l_Lean_Compiler_mkNatLe___closed__4;
x_3 = lean_array_push(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_mkNatLe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = l_Lean_Compiler_mkNatLe___closed__5;
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_array_push(x_4, x_2);
x_6 = l_Lean_Compiler_mkNatLe___closed__1;
x_7 = l_Lean_mkAppN(x_6, x_5);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Compiler_toDecidableExpr_match__1___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
if (x_2 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_4, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
else
{
lean_dec(x_4);
lean_dec(x_3);
if (x_2 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_apply_1(x_6, x_11);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_13 = lean_box(0);
x_14 = lean_apply_1(x_5, x_13);
return x_14;
}
}
}
}
lean_object* l_Lean_Compiler_toDecidableExpr_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_toDecidableExpr_match__1___rarg___boxed), 6, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_toDecidableExpr_match__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Compiler_toDecidableExpr_match__1___rarg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_neutralExpr;
x_2 = l_Lean_mkDecIsFalse(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_toDecidableExpr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_neutralExpr;
x_2 = l_Lean_mkDecIsTrue(x_1, x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_toDecidableExpr(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_toDecidableExpr___closed__1;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_toDecidableExpr___closed__2;
return x_5;
}
}
else
{
if (x_3 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_2);
x_6 = l_Lean_Compiler_mkLcProof(x_2);
x_7 = l_Lean_mkDecIsFalse(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_8 = l_Lean_Compiler_mkLcProof(x_2);
x_9 = l_Lean_mkDecIsTrue(x_2, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Compiler_toDecidableExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Compiler_toDecidableExpr(x_4, x_2, x_5);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldNatBinPred(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = lean_get_num_lit(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_5);
x_9 = lean_get_num_lit(x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_apply_2(x_1, x_4, x_5);
x_14 = lean_apply_2(x_2, x_8, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_Lean_Compiler_toDecidableExpr(x_3, x_13, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_apply_2(x_1, x_4, x_5);
x_19 = lean_apply_2(x_2, x_8, x_17);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
x_21 = l_Lean_Compiler_toDecidableExpr(x_3, x_18, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Lean_Compiler_foldNatBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Compiler_foldNatBinPred(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatEq), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldNatDecEq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_foldNatDecEq___closed__1;
x_5 = l_Lean_Position_lt___closed__1;
x_6 = l_Lean_Compiler_foldNatBinPred(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldNatDecEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecEq(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecLt___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatLt), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldNatDecLt(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_foldNatDecLt___closed__1;
x_5 = l_Lean_Position_lt___closed__2;
x_6 = l_Lean_Compiler_foldNatBinPred(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldNatDecLt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecLt(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecLe___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatLe), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_foldNatDecLe___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Nat_decLe___boxed), 2, 0);
return x_1;
}
}
lean_object* l_Lean_Compiler_foldNatDecLe(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = l_Lean_Compiler_foldNatDecLe___closed__1;
x_5 = l_Lean_Compiler_foldNatDecLe___closed__2;
x_6 = l_Lean_Compiler_foldNatBinPred(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
lean_object* l_Lean_Compiler_foldNatDecLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecLe(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatAdd___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__1;
x_2 = l_Lean_Compiler_natFoldFns___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMul___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__4;
x_2 = l_Lean_Compiler_natFoldFns___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__9;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDiv___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__7;
x_2 = l_Lean_Compiler_natFoldFns___closed__8;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_preUIntBinFoldFns___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMod___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__10;
x_2 = l_Lean_Compiler_natFoldFns___closed__11;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("pow");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_natFoldFns___closed__13;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__15() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatPow___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__14;
x_2 = l_Lean_Compiler_natFoldFns___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_main");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__14;
x_2 = l_Lean_Compiler_natFoldFns___closed__17;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__18;
x_2 = l_Lean_Compiler_natFoldFns___closed__15;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__20() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decEq");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_natFoldFns___closed__20;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecEq___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__21;
x_2 = l_Lean_Compiler_natFoldFns___closed__22;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decLt");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_natFoldFns___closed__24;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__26() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLt___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__25;
x_2 = l_Lean_Compiler_natFoldFns___closed__26;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("decLe");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_natFoldFns___closed__28;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLe___boxed), 3, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__29;
x_2 = l_Lean_Compiler_natFoldFns___closed__30;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_natFoldFns___closed__31;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__27;
x_2 = l_Lean_Compiler_natFoldFns___closed__32;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__23;
x_2 = l_Lean_Compiler_natFoldFns___closed__33;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__19;
x_2 = l_Lean_Compiler_natFoldFns___closed__34;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__16;
x_2 = l_Lean_Compiler_natFoldFns___closed__35;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__12;
x_2 = l_Lean_Compiler_natFoldFns___closed__36;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__9;
x_2 = l_Lean_Compiler_natFoldFns___closed__37;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__39() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__6;
x_2 = l_Lean_Compiler_natFoldFns___closed__38;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_natFoldFns___closed__3;
x_2 = l_Lean_Compiler_natFoldFns___closed__39;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_natFoldFns___closed__40;
return x_1;
}
}
lean_object* l_Lean_Compiler_getBoolLit_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
x_9 = !lean_is_exclusive(x_5);
if (x_9 == 0)
{
uint64_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_11 = lean_ctor_get(x_5, 1);
x_12 = lean_ctor_get_usize(x_5, 2);
x_13 = lean_ctor_get(x_5, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; size_t x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_6, 1);
x_16 = lean_ctor_get_usize(x_6, 2);
x_17 = lean_ctor_get(x_6, 0);
lean_dec(x_17);
x_18 = l_Lean_instQuoteBool___closed__1;
x_19 = lean_string_dec_eq(x_15, x_18);
lean_dec(x_15);
if (x_19 == 0)
{
lean_object* x_20; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_apply_1(x_4, x_1);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_1, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_1, 0);
lean_dec(x_23);
x_24 = l_instReprBool___closed__3;
x_25 = lean_string_dec_eq(x_11, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
lean_dec(x_2);
x_26 = l_instReprBool___closed__1;
x_27 = lean_string_dec_eq(x_11, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_18);
x_28 = lean_apply_1(x_4, x_1);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_1);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
x_29 = lean_box_uint64(x_10);
x_30 = lean_box_usize(x_16);
x_31 = lean_box_usize(x_12);
x_32 = lean_apply_4(x_3, x_8, x_29, x_30, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_1);
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box_uint64(x_10);
x_34 = lean_box_usize(x_16);
x_35 = lean_box_usize(x_12);
x_36 = lean_apply_4(x_2, x_8, x_33, x_34, x_35);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_dec(x_1);
x_37 = l_instReprBool___closed__3;
x_38 = lean_string_dec_eq(x_11, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_2);
x_39 = l_instReprBool___closed__1;
x_40 = lean_string_dec_eq(x_11, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_3);
lean_ctor_set(x_6, 1, x_18);
x_41 = lean_alloc_ctor(4, 2, 8);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_8);
lean_ctor_set_uint64(x_41, sizeof(void*)*2, x_10);
x_42 = lean_apply_1(x_4, x_41);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
x_43 = lean_box_uint64(x_10);
x_44 = lean_box_usize(x_16);
x_45 = lean_box_usize(x_12);
x_46 = lean_apply_4(x_3, x_8, x_43, x_44, x_45);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_6);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_47 = lean_box_uint64(x_10);
x_48 = lean_box_usize(x_16);
x_49 = lean_box_usize(x_12);
x_50 = lean_apply_4(x_2, x_8, x_47, x_48, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_6, 1);
x_52 = lean_ctor_get_usize(x_6, 2);
lean_inc(x_51);
lean_dec(x_6);
x_53 = l_Lean_instQuoteBool___closed__1;
x_54 = lean_string_dec_eq(x_51, x_53);
lean_dec(x_51);
if (x_54 == 0)
{
lean_object* x_55; 
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_55 = lean_apply_1(x_4, x_1);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_56 = x_1;
} else {
 lean_dec_ref(x_1);
 x_56 = lean_box(0);
}
x_57 = l_instReprBool___closed__3;
x_58 = lean_string_dec_eq(x_11, x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_2);
x_59 = l_instReprBool___closed__1;
x_60 = lean_string_dec_eq(x_11, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_3);
x_61 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_61, 0, x_7);
lean_ctor_set(x_61, 1, x_53);
lean_ctor_set_usize(x_61, 2, x_52);
lean_ctor_set(x_5, 0, x_61);
if (lean_is_scalar(x_56)) {
 x_62 = lean_alloc_ctor(4, 2, 8);
} else {
 x_62 = x_56;
}
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_8);
lean_ctor_set_uint64(x_62, sizeof(void*)*2, x_10);
x_63 = lean_apply_1(x_4, x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_56);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
x_64 = lean_box_uint64(x_10);
x_65 = lean_box_usize(x_52);
x_66 = lean_box_usize(x_12);
x_67 = lean_apply_4(x_3, x_8, x_64, x_65, x_66);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_56);
lean_free_object(x_5);
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
x_68 = lean_box_uint64(x_10);
x_69 = lean_box_usize(x_52);
x_70 = lean_box_usize(x_12);
x_71 = lean_apply_4(x_2, x_8, x_68, x_69, x_70);
return x_71;
}
}
}
}
else
{
uint64_t x_72; lean_object* x_73; size_t x_74; lean_object* x_75; size_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_72 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_73 = lean_ctor_get(x_5, 1);
x_74 = lean_ctor_get_usize(x_5, 2);
lean_inc(x_73);
lean_dec(x_5);
x_75 = lean_ctor_get(x_6, 1);
lean_inc(x_75);
x_76 = lean_ctor_get_usize(x_6, 2);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_77 = x_6;
} else {
 lean_dec_ref(x_6);
 x_77 = lean_box(0);
}
x_78 = l_Lean_instQuoteBool___closed__1;
x_79 = lean_string_dec_eq(x_75, x_78);
lean_dec(x_75);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_80 = lean_apply_1(x_4, x_1);
return x_80;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_81 = x_1;
} else {
 lean_dec_ref(x_1);
 x_81 = lean_box(0);
}
x_82 = l_instReprBool___closed__3;
x_83 = lean_string_dec_eq(x_73, x_82);
if (x_83 == 0)
{
lean_object* x_84; uint8_t x_85; 
lean_dec(x_2);
x_84 = l_instReprBool___closed__1;
x_85 = lean_string_dec_eq(x_73, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_3);
if (lean_is_scalar(x_77)) {
 x_86 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
} else {
 x_86 = x_77;
}
lean_ctor_set(x_86, 0, x_7);
lean_ctor_set(x_86, 1, x_78);
lean_ctor_set_usize(x_86, 2, x_76);
x_87 = lean_alloc_ctor(1, 2, sizeof(size_t)*1);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_73);
lean_ctor_set_usize(x_87, 2, x_74);
if (lean_is_scalar(x_81)) {
 x_88 = lean_alloc_ctor(4, 2, 8);
} else {
 x_88 = x_81;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_8);
lean_ctor_set_uint64(x_88, sizeof(void*)*2, x_72);
x_89 = lean_apply_1(x_4, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_4);
x_90 = lean_box_uint64(x_72);
x_91 = lean_box_usize(x_76);
x_92 = lean_box_usize(x_74);
x_93 = lean_apply_4(x_3, x_8, x_90, x_91, x_92);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_73);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_box_uint64(x_72);
x_95 = lean_box_usize(x_76);
x_96 = lean_box_usize(x_74);
x_97 = lean_apply_4(x_2, x_8, x_94, x_95, x_96);
return x_97;
}
}
}
}
else
{
lean_object* x_98; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_98 = lean_apply_1(x_4, x_1);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_99 = lean_apply_1(x_4, x_1);
return x_99;
}
}
else
{
lean_object* x_100; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_100 = lean_apply_1(x_4, x_1);
return x_100;
}
}
else
{
lean_object* x_101; 
lean_dec(x_3);
lean_dec(x_2);
x_101 = lean_apply_1(x_4, x_1);
return x_101;
}
}
}
lean_object* l_Lean_Compiler_getBoolLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_getBoolLit_match__1___rarg), 4, 0);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_getBoolLit___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_getBoolLit___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_getBoolLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 1);
x_7 = l_Lean_instQuoteBool___closed__1;
x_8 = lean_string_dec_eq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_instReprBool___closed__3;
x_11 = lean_string_dec_eq(x_5, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_instReprBool___closed__1;
x_13 = lean_string_dec_eq(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = l_Lean_Compiler_getBoolLit___closed__1;
return x_15;
}
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_getBoolLit___closed__2;
return x_16;
}
}
}
else
{
lean_object* x_17; 
x_17 = lean_box(0);
return x_17;
}
}
else
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
return x_20;
}
}
}
lean_object* l_Lean_Compiler_getBoolLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_getBoolLit(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldStrictAnd_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
x_8 = lean_apply_2(x_7, x_2, x_2);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_7);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_5);
x_11 = lean_apply_1(x_6, x_1);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_6);
x_12 = lean_apply_1(x_5, x_1);
return x_12;
}
}
}
else
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_unbox(x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_3);
x_15 = lean_apply_1(x_4, x_2);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_4);
x_16 = lean_apply_1(x_3, x_2);
return x_16;
}
}
}
}
lean_object* l_Lean_Compiler_foldStrictAnd_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictAnd_match__1___rarg), 7, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldStrictAnd___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getBoolLit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_getBoolLit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
}
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Compiler_foldStrictAnd(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictAnd___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldStrictAnd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldStrictAnd(x_2);
return x_3;
}
}
lean_object* l_Lean_Compiler_foldStrictOr___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getBoolLit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_getBoolLit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
}
}
}
}
lean_object* l_Lean_Compiler_foldStrictOr(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictOr___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldStrictOr___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldStrictOr(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strictOr");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_boolFoldFns___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictOr___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_boolFoldFns___closed__2;
x_2 = l_Lean_Compiler_boolFoldFns___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("strictAnd");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_boolFoldFns___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictAnd___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_boolFoldFns___closed__6;
x_2 = l_Lean_Compiler_boolFoldFns___closed__7;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_boolFoldFns___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_boolFoldFns___closed__4;
x_2 = l_Lean_Compiler_boolFoldFns___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_boolFoldFns___closed__10;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_binFoldFns___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_boolFoldFns;
x_2 = l_Lean_Compiler_uintBinFoldFns;
x_3 = l_List_append___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_binFoldFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_binFoldFns___closed__1;
x_2 = l_Lean_Compiler_natFoldFns;
x_3 = l_List_append___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_binFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_binFoldFns___closed__2;
return x_1;
}
}
lean_object* l_Lean_Compiler_foldNatSucc___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_num_lit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_mkNatLit(x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_mkNatLit(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
lean_object* l_Lean_Compiler_foldNatSucc(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatSucc___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldNatSucc___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldNatSucc(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_foldCharOfNat___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Compiler_mkUInt32Lit(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_foldCharOfNat___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_foldCharOfNat___closed__1;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldCharOfNat(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; 
x_3 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_uint32_of_nat(x_6);
x_8 = 55296;
x_9 = x_7 < x_8;
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 57343;
x_11 = x_10 < x_7;
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_3);
lean_dec(x_6);
x_12 = l_Lean_Compiler_foldCharOfNat___closed__2;
return x_12;
}
else
{
uint32_t x_13; uint8_t x_14; 
x_13 = 1114112;
x_14 = x_7 < x_13;
if (x_14 == 0)
{
lean_object* x_15; 
lean_free_object(x_3);
lean_dec(x_6);
x_15 = l_Lean_Compiler_foldCharOfNat___closed__2;
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Compiler_mkUInt32Lit(x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_16);
return x_3;
}
}
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Compiler_mkUInt32Lit(x_6);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_17);
return x_3;
}
}
else
{
lean_object* x_18; uint32_t x_19; uint32_t x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_uint32_of_nat(x_18);
x_20 = 55296;
x_21 = x_19 < x_20;
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 57343;
x_23 = x_22 < x_19;
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_18);
x_24 = l_Lean_Compiler_foldCharOfNat___closed__2;
return x_24;
}
else
{
uint32_t x_25; uint8_t x_26; 
x_25 = 1114112;
x_26 = x_19 < x_25;
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_18);
x_27 = l_Lean_Compiler_foldCharOfNat___closed__2;
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_Compiler_mkUInt32Lit(x_18);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Compiler_mkUInt32Lit(x_18);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_2);
x_32 = lean_box(0);
return x_32;
}
}
}
lean_object* l_Lean_Compiler_foldCharOfNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_foldCharOfNat(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Compiler_foldToNat___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_num_lit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_Lean_mkNatLit(x_5);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_mkNatLit(x_7);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
}
}
}
lean_object* l_Lean_Compiler_foldToNat(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldToNat___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldToNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Compiler_foldToNat(x_2);
return x_3;
}
}
static lean_object* _init_l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldToNat___boxed), 1, 0);
return x_1;
}
}
lean_object* l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1;
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_8);
x_1 = x_2;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1;
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_1);
x_1 = x_15;
x_2 = x_11;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_uintFoldToNatFns___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes;
x_3 = l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_uintFoldToNatFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_uintFoldToNatFns___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("succ");
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Literal_type___closed__2;
x_2 = l_Lean_Compiler_unFoldFns___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatSucc___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_unFoldFns___closed__2;
x_2 = l_Lean_Compiler_unFoldFns___closed__3;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_foldCharOfNat___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_isCharLit___closed__4;
x_2 = l_Lean_Compiler_unFoldFns___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_unFoldFns___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_unFoldFns___closed__4;
x_2 = l_Lean_Compiler_unFoldFns___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Compiler_unFoldFns___closed__8;
x_2 = l_Lean_Compiler_uintFoldToNatFns;
x_3 = l_List_append___rarg(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_unFoldFns___closed__9;
return x_1;
}
}
lean_object* l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_name_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
lean_object* l_Lean_Compiler_findBinFoldFn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_binFoldFns;
x_3 = l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Compiler_findBinFoldFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_findBinFoldFn(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_name_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
lean_object* l_Lean_Compiler_findUnFoldFn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_unFoldFns;
x_3 = l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(x_1, x_2);
return x_3;
}
}
lean_object* l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Compiler_findUnFoldFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_findUnFoldFn(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Compiler_foldBinOp_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
lean_dec(x_1);
x_7 = lean_box_uint64(x_6);
x_8 = lean_apply_3(x_2, x_4, x_5, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_apply_1(x_3, x_1);
return x_9;
}
}
}
lean_object* l_Lean_Compiler_foldBinOp_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_foldBinOp_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* lean_fold_bin_op(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Compiler_binFoldFns;
x_7 = l_List_lookup___at_Lean_Compiler_findBinFoldFn___spec__1(x_5, x_6);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(x_1);
x_11 = lean_apply_3(x_9, x_10, x_3, x_4);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_box(0);
return x_12;
}
}
}
lean_object* l_Lean_Compiler_foldBinOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_fold_bin_op(x_5, x_2, x_3, x_4);
return x_6;
}
}
lean_object* lean_fold_un_op(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Compiler_unFoldFns;
x_6 = l_List_lookup___at_Lean_Compiler_findUnFoldFn___spec__1(x_4, x_5);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(x_1);
x_10 = lean_apply_2(x_8, x_9, x_3);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
lean_object* l_Lean_Compiler_foldUnOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_fold_un_op(x_4, x_2, x_3);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Expr(lean_object*);
lean_object* initialize_Lean_Compiler_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Compiler_ConstFolding(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Expr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_mkUIntTypeName___closed__1 = _init_l_Lean_Compiler_mkUIntTypeName___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkUIntTypeName___closed__1);
l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1 = _init_l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1();
lean_mark_persistent(l_Lean_Compiler_NumScalarTypeInfo_toNatFn___default___closed__1);
l_Lean_Compiler_numScalarTypes___closed__1 = _init_l_Lean_Compiler_numScalarTypes___closed__1();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__1);
l_Lean_Compiler_numScalarTypes___closed__2 = _init_l_Lean_Compiler_numScalarTypes___closed__2();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__2);
l_Lean_Compiler_numScalarTypes___closed__3 = _init_l_Lean_Compiler_numScalarTypes___closed__3();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__3);
l_Lean_Compiler_numScalarTypes___closed__4 = _init_l_Lean_Compiler_numScalarTypes___closed__4();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__4);
l_Lean_Compiler_numScalarTypes___closed__5 = _init_l_Lean_Compiler_numScalarTypes___closed__5();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__5);
l_Lean_Compiler_numScalarTypes___closed__6 = _init_l_Lean_Compiler_numScalarTypes___closed__6();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__6);
l_Lean_Compiler_numScalarTypes___closed__7 = _init_l_Lean_Compiler_numScalarTypes___closed__7();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__7);
l_Lean_Compiler_numScalarTypes___closed__8 = _init_l_Lean_Compiler_numScalarTypes___closed__8();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__8);
l_Lean_Compiler_numScalarTypes___closed__9 = _init_l_Lean_Compiler_numScalarTypes___closed__9();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__9);
l_Lean_Compiler_numScalarTypes___closed__10 = _init_l_Lean_Compiler_numScalarTypes___closed__10();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__10);
l_Lean_Compiler_numScalarTypes___closed__11 = _init_l_Lean_Compiler_numScalarTypes___closed__11();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__11);
l_Lean_Compiler_numScalarTypes___closed__12 = _init_l_Lean_Compiler_numScalarTypes___closed__12();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__12);
l_Lean_Compiler_numScalarTypes___closed__13 = _init_l_Lean_Compiler_numScalarTypes___closed__13();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__13);
l_Lean_Compiler_numScalarTypes___closed__14 = _init_l_Lean_Compiler_numScalarTypes___closed__14();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__14);
l_Lean_Compiler_numScalarTypes___closed__15 = _init_l_Lean_Compiler_numScalarTypes___closed__15();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__15);
l_Lean_Compiler_numScalarTypes___closed__16 = _init_l_Lean_Compiler_numScalarTypes___closed__16();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__16);
l_Lean_Compiler_numScalarTypes___closed__17 = _init_l_Lean_Compiler_numScalarTypes___closed__17();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__17);
l_Lean_Compiler_numScalarTypes___closed__18 = _init_l_Lean_Compiler_numScalarTypes___closed__18();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__18);
l_Lean_Compiler_numScalarTypes___closed__19 = _init_l_Lean_Compiler_numScalarTypes___closed__19();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__19);
l_Lean_Compiler_numScalarTypes___closed__20 = _init_l_Lean_Compiler_numScalarTypes___closed__20();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__20);
l_Lean_Compiler_numScalarTypes___closed__21 = _init_l_Lean_Compiler_numScalarTypes___closed__21();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__21);
l_Lean_Compiler_numScalarTypes___closed__22 = _init_l_Lean_Compiler_numScalarTypes___closed__22();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__22);
l_Lean_Compiler_numScalarTypes___closed__23 = _init_l_Lean_Compiler_numScalarTypes___closed__23();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__23);
l_Lean_Compiler_numScalarTypes___closed__24 = _init_l_Lean_Compiler_numScalarTypes___closed__24();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__24);
l_Lean_Compiler_numScalarTypes___closed__25 = _init_l_Lean_Compiler_numScalarTypes___closed__25();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__25);
l_Lean_Compiler_numScalarTypes___closed__26 = _init_l_Lean_Compiler_numScalarTypes___closed__26();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes___closed__26);
l_Lean_Compiler_numScalarTypes = _init_l_Lean_Compiler_numScalarTypes();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes);
l_Lean_Compiler_foldUIntAdd___closed__1 = _init_l_Lean_Compiler_foldUIntAdd___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntAdd___closed__1);
l_Lean_Compiler_foldUIntMul___closed__1 = _init_l_Lean_Compiler_foldUIntMul___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntMul___closed__1);
l_Lean_Compiler_foldUIntDiv___closed__1 = _init_l_Lean_Compiler_foldUIntDiv___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntDiv___closed__1);
l_Lean_Compiler_foldUIntMod___closed__1 = _init_l_Lean_Compiler_foldUIntMod___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntMod___closed__1);
l_Lean_Compiler_foldUIntSub___closed__1 = _init_l_Lean_Compiler_foldUIntSub___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldUIntSub___closed__1);
l_Lean_Compiler_preUIntBinFoldFns___closed__1 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__1);
l_Lean_Compiler_preUIntBinFoldFns___closed__2 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__2);
l_Lean_Compiler_preUIntBinFoldFns___closed__3 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__3();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__3);
l_Lean_Compiler_preUIntBinFoldFns___closed__4 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__4();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__4);
l_Lean_Compiler_preUIntBinFoldFns___closed__5 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__5();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__5);
l_Lean_Compiler_preUIntBinFoldFns___closed__6 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__6();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__6);
l_Lean_Compiler_preUIntBinFoldFns___closed__7 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__7();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__7);
l_Lean_Compiler_preUIntBinFoldFns___closed__8 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__8();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__8);
l_Lean_Compiler_preUIntBinFoldFns___closed__9 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__9();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__9);
l_Lean_Compiler_preUIntBinFoldFns___closed__10 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__10();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__10);
l_Lean_Compiler_preUIntBinFoldFns___closed__11 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__11();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__11);
l_Lean_Compiler_preUIntBinFoldFns___closed__12 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__12();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__12);
l_Lean_Compiler_preUIntBinFoldFns___closed__13 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__13();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__13);
l_Lean_Compiler_preUIntBinFoldFns___closed__14 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__14();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__14);
l_Lean_Compiler_preUIntBinFoldFns___closed__15 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__15();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__15);
l_Lean_Compiler_preUIntBinFoldFns___closed__16 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__16();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__16);
l_Lean_Compiler_preUIntBinFoldFns___closed__17 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__17();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__17);
l_Lean_Compiler_preUIntBinFoldFns___closed__18 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__18();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__18);
l_Lean_Compiler_preUIntBinFoldFns___closed__19 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__19();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__19);
l_Lean_Compiler_preUIntBinFoldFns___closed__20 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__20();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__20);
l_Lean_Compiler_preUIntBinFoldFns___closed__21 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__21();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__21);
l_Lean_Compiler_preUIntBinFoldFns___closed__22 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__22();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__22);
l_Lean_Compiler_preUIntBinFoldFns___closed__23 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__23();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__23);
l_Lean_Compiler_preUIntBinFoldFns___closed__24 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__24();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__24);
l_Lean_Compiler_preUIntBinFoldFns___closed__25 = _init_l_Lean_Compiler_preUIntBinFoldFns___closed__25();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns___closed__25);
l_Lean_Compiler_preUIntBinFoldFns = _init_l_Lean_Compiler_preUIntBinFoldFns();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns);
l_Lean_Compiler_uintBinFoldFns___closed__1 = _init_l_Lean_Compiler_uintBinFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_uintBinFoldFns___closed__1);
l_Lean_Compiler_uintBinFoldFns = _init_l_Lean_Compiler_uintBinFoldFns();
lean_mark_persistent(l_Lean_Compiler_uintBinFoldFns);
l_Lean_Compiler_natPowThreshold = _init_l_Lean_Compiler_natPowThreshold();
lean_mark_persistent(l_Lean_Compiler_natPowThreshold);
l_Lean_Compiler_mkNatEq___closed__1 = _init_l_Lean_Compiler_mkNatEq___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__1);
l_Lean_Compiler_mkNatEq___closed__2 = _init_l_Lean_Compiler_mkNatEq___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__2);
l_Lean_Compiler_mkNatEq___closed__3 = _init_l_Lean_Compiler_mkNatEq___closed__3();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__3);
l_Lean_Compiler_mkNatEq___closed__4 = _init_l_Lean_Compiler_mkNatEq___closed__4();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__4);
l_Lean_Compiler_mkNatEq___closed__5 = _init_l_Lean_Compiler_mkNatEq___closed__5();
lean_mark_persistent(l_Lean_Compiler_mkNatEq___closed__5);
l_Lean_Compiler_mkNatLt___closed__1 = _init_l_Lean_Compiler_mkNatLt___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__1);
l_Lean_Compiler_mkNatLt___closed__2 = _init_l_Lean_Compiler_mkNatLt___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__2);
l_Lean_Compiler_mkNatLt___closed__3 = _init_l_Lean_Compiler_mkNatLt___closed__3();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__3);
l_Lean_Compiler_mkNatLt___closed__4 = _init_l_Lean_Compiler_mkNatLt___closed__4();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__4);
l_Lean_Compiler_mkNatLt___closed__5 = _init_l_Lean_Compiler_mkNatLt___closed__5();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__5);
l_Lean_Compiler_mkNatLt___closed__6 = _init_l_Lean_Compiler_mkNatLt___closed__6();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__6);
l_Lean_Compiler_mkNatLt___closed__7 = _init_l_Lean_Compiler_mkNatLt___closed__7();
lean_mark_persistent(l_Lean_Compiler_mkNatLt___closed__7);
l_Lean_Compiler_mkNatLe___closed__1 = _init_l_Lean_Compiler_mkNatLe___closed__1();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__1);
l_Lean_Compiler_mkNatLe___closed__2 = _init_l_Lean_Compiler_mkNatLe___closed__2();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__2);
l_Lean_Compiler_mkNatLe___closed__3 = _init_l_Lean_Compiler_mkNatLe___closed__3();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__3);
l_Lean_Compiler_mkNatLe___closed__4 = _init_l_Lean_Compiler_mkNatLe___closed__4();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__4);
l_Lean_Compiler_mkNatLe___closed__5 = _init_l_Lean_Compiler_mkNatLe___closed__5();
lean_mark_persistent(l_Lean_Compiler_mkNatLe___closed__5);
l_Lean_Compiler_toDecidableExpr___closed__1 = _init_l_Lean_Compiler_toDecidableExpr___closed__1();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__1);
l_Lean_Compiler_toDecidableExpr___closed__2 = _init_l_Lean_Compiler_toDecidableExpr___closed__2();
lean_mark_persistent(l_Lean_Compiler_toDecidableExpr___closed__2);
l_Lean_Compiler_foldNatDecEq___closed__1 = _init_l_Lean_Compiler_foldNatDecEq___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatDecEq___closed__1);
l_Lean_Compiler_foldNatDecLt___closed__1 = _init_l_Lean_Compiler_foldNatDecLt___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatDecLt___closed__1);
l_Lean_Compiler_foldNatDecLe___closed__1 = _init_l_Lean_Compiler_foldNatDecLe___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldNatDecLe___closed__1);
l_Lean_Compiler_foldNatDecLe___closed__2 = _init_l_Lean_Compiler_foldNatDecLe___closed__2();
lean_mark_persistent(l_Lean_Compiler_foldNatDecLe___closed__2);
l_Lean_Compiler_natFoldFns___closed__1 = _init_l_Lean_Compiler_natFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__1);
l_Lean_Compiler_natFoldFns___closed__2 = _init_l_Lean_Compiler_natFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__2);
l_Lean_Compiler_natFoldFns___closed__3 = _init_l_Lean_Compiler_natFoldFns___closed__3();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__3);
l_Lean_Compiler_natFoldFns___closed__4 = _init_l_Lean_Compiler_natFoldFns___closed__4();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__4);
l_Lean_Compiler_natFoldFns___closed__5 = _init_l_Lean_Compiler_natFoldFns___closed__5();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__5);
l_Lean_Compiler_natFoldFns___closed__6 = _init_l_Lean_Compiler_natFoldFns___closed__6();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__6);
l_Lean_Compiler_natFoldFns___closed__7 = _init_l_Lean_Compiler_natFoldFns___closed__7();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__7);
l_Lean_Compiler_natFoldFns___closed__8 = _init_l_Lean_Compiler_natFoldFns___closed__8();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__8);
l_Lean_Compiler_natFoldFns___closed__9 = _init_l_Lean_Compiler_natFoldFns___closed__9();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__9);
l_Lean_Compiler_natFoldFns___closed__10 = _init_l_Lean_Compiler_natFoldFns___closed__10();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__10);
l_Lean_Compiler_natFoldFns___closed__11 = _init_l_Lean_Compiler_natFoldFns___closed__11();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__11);
l_Lean_Compiler_natFoldFns___closed__12 = _init_l_Lean_Compiler_natFoldFns___closed__12();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__12);
l_Lean_Compiler_natFoldFns___closed__13 = _init_l_Lean_Compiler_natFoldFns___closed__13();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__13);
l_Lean_Compiler_natFoldFns___closed__14 = _init_l_Lean_Compiler_natFoldFns___closed__14();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__14);
l_Lean_Compiler_natFoldFns___closed__15 = _init_l_Lean_Compiler_natFoldFns___closed__15();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__15);
l_Lean_Compiler_natFoldFns___closed__16 = _init_l_Lean_Compiler_natFoldFns___closed__16();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__16);
l_Lean_Compiler_natFoldFns___closed__17 = _init_l_Lean_Compiler_natFoldFns___closed__17();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__17);
l_Lean_Compiler_natFoldFns___closed__18 = _init_l_Lean_Compiler_natFoldFns___closed__18();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__18);
l_Lean_Compiler_natFoldFns___closed__19 = _init_l_Lean_Compiler_natFoldFns___closed__19();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__19);
l_Lean_Compiler_natFoldFns___closed__20 = _init_l_Lean_Compiler_natFoldFns___closed__20();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__20);
l_Lean_Compiler_natFoldFns___closed__21 = _init_l_Lean_Compiler_natFoldFns___closed__21();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__21);
l_Lean_Compiler_natFoldFns___closed__22 = _init_l_Lean_Compiler_natFoldFns___closed__22();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__22);
l_Lean_Compiler_natFoldFns___closed__23 = _init_l_Lean_Compiler_natFoldFns___closed__23();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__23);
l_Lean_Compiler_natFoldFns___closed__24 = _init_l_Lean_Compiler_natFoldFns___closed__24();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__24);
l_Lean_Compiler_natFoldFns___closed__25 = _init_l_Lean_Compiler_natFoldFns___closed__25();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__25);
l_Lean_Compiler_natFoldFns___closed__26 = _init_l_Lean_Compiler_natFoldFns___closed__26();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__26);
l_Lean_Compiler_natFoldFns___closed__27 = _init_l_Lean_Compiler_natFoldFns___closed__27();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__27);
l_Lean_Compiler_natFoldFns___closed__28 = _init_l_Lean_Compiler_natFoldFns___closed__28();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__28);
l_Lean_Compiler_natFoldFns___closed__29 = _init_l_Lean_Compiler_natFoldFns___closed__29();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__29);
l_Lean_Compiler_natFoldFns___closed__30 = _init_l_Lean_Compiler_natFoldFns___closed__30();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__30);
l_Lean_Compiler_natFoldFns___closed__31 = _init_l_Lean_Compiler_natFoldFns___closed__31();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__31);
l_Lean_Compiler_natFoldFns___closed__32 = _init_l_Lean_Compiler_natFoldFns___closed__32();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__32);
l_Lean_Compiler_natFoldFns___closed__33 = _init_l_Lean_Compiler_natFoldFns___closed__33();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__33);
l_Lean_Compiler_natFoldFns___closed__34 = _init_l_Lean_Compiler_natFoldFns___closed__34();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__34);
l_Lean_Compiler_natFoldFns___closed__35 = _init_l_Lean_Compiler_natFoldFns___closed__35();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__35);
l_Lean_Compiler_natFoldFns___closed__36 = _init_l_Lean_Compiler_natFoldFns___closed__36();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__36);
l_Lean_Compiler_natFoldFns___closed__37 = _init_l_Lean_Compiler_natFoldFns___closed__37();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__37);
l_Lean_Compiler_natFoldFns___closed__38 = _init_l_Lean_Compiler_natFoldFns___closed__38();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__38);
l_Lean_Compiler_natFoldFns___closed__39 = _init_l_Lean_Compiler_natFoldFns___closed__39();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__39);
l_Lean_Compiler_natFoldFns___closed__40 = _init_l_Lean_Compiler_natFoldFns___closed__40();
lean_mark_persistent(l_Lean_Compiler_natFoldFns___closed__40);
l_Lean_Compiler_natFoldFns = _init_l_Lean_Compiler_natFoldFns();
lean_mark_persistent(l_Lean_Compiler_natFoldFns);
l_Lean_Compiler_getBoolLit___closed__1 = _init_l_Lean_Compiler_getBoolLit___closed__1();
lean_mark_persistent(l_Lean_Compiler_getBoolLit___closed__1);
l_Lean_Compiler_getBoolLit___closed__2 = _init_l_Lean_Compiler_getBoolLit___closed__2();
lean_mark_persistent(l_Lean_Compiler_getBoolLit___closed__2);
l_Lean_Compiler_boolFoldFns___closed__1 = _init_l_Lean_Compiler_boolFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__1);
l_Lean_Compiler_boolFoldFns___closed__2 = _init_l_Lean_Compiler_boolFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__2);
l_Lean_Compiler_boolFoldFns___closed__3 = _init_l_Lean_Compiler_boolFoldFns___closed__3();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__3);
l_Lean_Compiler_boolFoldFns___closed__4 = _init_l_Lean_Compiler_boolFoldFns___closed__4();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__4);
l_Lean_Compiler_boolFoldFns___closed__5 = _init_l_Lean_Compiler_boolFoldFns___closed__5();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__5);
l_Lean_Compiler_boolFoldFns___closed__6 = _init_l_Lean_Compiler_boolFoldFns___closed__6();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__6);
l_Lean_Compiler_boolFoldFns___closed__7 = _init_l_Lean_Compiler_boolFoldFns___closed__7();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__7);
l_Lean_Compiler_boolFoldFns___closed__8 = _init_l_Lean_Compiler_boolFoldFns___closed__8();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__8);
l_Lean_Compiler_boolFoldFns___closed__9 = _init_l_Lean_Compiler_boolFoldFns___closed__9();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__9);
l_Lean_Compiler_boolFoldFns___closed__10 = _init_l_Lean_Compiler_boolFoldFns___closed__10();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns___closed__10);
l_Lean_Compiler_boolFoldFns = _init_l_Lean_Compiler_boolFoldFns();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns);
l_Lean_Compiler_binFoldFns___closed__1 = _init_l_Lean_Compiler_binFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_binFoldFns___closed__1);
l_Lean_Compiler_binFoldFns___closed__2 = _init_l_Lean_Compiler_binFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_binFoldFns___closed__2);
l_Lean_Compiler_binFoldFns = _init_l_Lean_Compiler_binFoldFns();
lean_mark_persistent(l_Lean_Compiler_binFoldFns);
l_Lean_Compiler_foldCharOfNat___closed__1 = _init_l_Lean_Compiler_foldCharOfNat___closed__1();
lean_mark_persistent(l_Lean_Compiler_foldCharOfNat___closed__1);
l_Lean_Compiler_foldCharOfNat___closed__2 = _init_l_Lean_Compiler_foldCharOfNat___closed__2();
lean_mark_persistent(l_Lean_Compiler_foldCharOfNat___closed__2);
l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1 = _init_l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1();
lean_mark_persistent(l_List_foldl___at_Lean_Compiler_uintFoldToNatFns___spec__1___closed__1);
l_Lean_Compiler_uintFoldToNatFns___closed__1 = _init_l_Lean_Compiler_uintFoldToNatFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_uintFoldToNatFns___closed__1);
l_Lean_Compiler_uintFoldToNatFns = _init_l_Lean_Compiler_uintFoldToNatFns();
lean_mark_persistent(l_Lean_Compiler_uintFoldToNatFns);
l_Lean_Compiler_unFoldFns___closed__1 = _init_l_Lean_Compiler_unFoldFns___closed__1();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__1);
l_Lean_Compiler_unFoldFns___closed__2 = _init_l_Lean_Compiler_unFoldFns___closed__2();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__2);
l_Lean_Compiler_unFoldFns___closed__3 = _init_l_Lean_Compiler_unFoldFns___closed__3();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__3);
l_Lean_Compiler_unFoldFns___closed__4 = _init_l_Lean_Compiler_unFoldFns___closed__4();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__4);
l_Lean_Compiler_unFoldFns___closed__5 = _init_l_Lean_Compiler_unFoldFns___closed__5();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__5);
l_Lean_Compiler_unFoldFns___closed__6 = _init_l_Lean_Compiler_unFoldFns___closed__6();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__6);
l_Lean_Compiler_unFoldFns___closed__7 = _init_l_Lean_Compiler_unFoldFns___closed__7();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__7);
l_Lean_Compiler_unFoldFns___closed__8 = _init_l_Lean_Compiler_unFoldFns___closed__8();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__8);
l_Lean_Compiler_unFoldFns___closed__9 = _init_l_Lean_Compiler_unFoldFns___closed__9();
lean_mark_persistent(l_Lean_Compiler_unFoldFns___closed__9);
l_Lean_Compiler_unFoldFns = _init_l_Lean_Compiler_unFoldFns();
lean_mark_persistent(l_Lean_Compiler_unFoldFns);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
