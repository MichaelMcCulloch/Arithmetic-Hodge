// Lean compiler output
// Module: ArithmeticHodge.Analysis.WeilDefs
// Imports: public import Init public import Mathlib.NumberTheory.ArithmeticFunction.Defs public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt public import Mathlib.Topology.Algebra.InfiniteSum.Basic public import Mathlib.MeasureTheory.Integral.IntegralEqImproper public import Mathlib.Analysis.SpecialFunctions.Log.Basic public import Mathlib.Data.Nat.Prime.Basic public import Mathlib.NumberTheory.LSeries.RiemannZeta public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_ArithmeticFunction_Defs(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_ArithmeticFunction_VonMangoldt(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Algebra_InfiniteSum_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_IntegralEqImproper(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Nat_Prime_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Gamma_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilDefs(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_ArithmeticFunction_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_ArithmeticFunction_VonMangoldt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Algebra_InfiniteSum_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_IntegralEqImproper(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Nat_Prime_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Gamma_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
