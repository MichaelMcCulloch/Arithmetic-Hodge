// Lean compiler output
// Module: ArithmeticHodge.Analysis.ZetaProduct
// Imports: public import Init public import ArithmeticHodge.Analysis.EntireFunction.Hadamard public import ArithmeticHodge.Analysis.WeilDefs public import Mathlib.NumberTheory.LSeries.RiemannZeta public import Mathlib.NumberTheory.LSeries.Nonvanishing public import Mathlib.Analysis.Normed.Module.Connected public import Mathlib.Topology.Compactness.Lindelof public import Mathlib.Topology.DiscreteSubset public import Mathlib.Analysis.Complex.CauchyIntegral public import Mathlib.Analysis.Analytic.Order
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
LEAN_EXPORT lean_object* lp_ArithmeticHodge___private_ArithmeticHodge_Analysis_ZetaProduct_0__ArithmeticHodge_Analysis_zetaZeroSeq_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ArithmeticHodge___private_ArithmeticHodge_Analysis_ZetaProduct_0__ArithmeticHodge_Analysis_zetaZeroSeq_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_ArithmeticHodge___private_ArithmeticHodge_Analysis_ZetaProduct_0__ArithmeticHodge_Analysis_zetaZeroSeq_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_ArithmeticHodge___private_ArithmeticHodge_Analysis_ZetaProduct_0__ArithmeticHodge_Analysis_zetaZeroSeq_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Hadamard(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilDefs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_LSeries_Nonvanishing(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Module_Connected(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Compactness_Lindelof(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_DiscreteSubset(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_CauchyIntegral(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Analytic_Order(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_ZetaProduct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Hadamard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_LSeries_Nonvanishing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Module_Connected(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Compactness_Lindelof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_DiscreteSubset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_CauchyIntegral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Analytic_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
