// Lean compiler output
// Module: ArithmeticHodge.Analysis.EntireFunction.Order
// Imports: public import Init public import Mathlib.Analysis.SpecialFunctions.Complex.Log public import Mathlib.Analysis.Complex.JensenFormula public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic public import Mathlib.Analysis.Meromorphic.Order public import Mathlib.Analysis.Meromorphic.TrailingCoefficient public import Mathlib.Analysis.Analytic.IsolatedZeros public import Mathlib.Topology.Algebra.InfiniteSum.Basic public import Mathlib.NumberTheory.LSeries.RiemannZeta public import Mathlib.NumberTheory.LSeries.Nonvanishing public import Mathlib.Analysis.SpecialFunctions.Log.Basic public import Mathlib.Analysis.SpecialFunctions.Pow.Real public import Mathlib.Order.Filter.Basic
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
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Log(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_JensenFormula(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_ValueDistribution_LogCounting_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Meromorphic_Order(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Meromorphic_TrailingCoefficient(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Analytic_IsolatedZeros(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Algebra_InfiniteSum_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_NumberTheory_LSeries_Nonvanishing(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Filter_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Order(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_JensenFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_ValueDistribution_LogCounting_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Meromorphic_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Meromorphic_TrailingCoefficient(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Analytic_IsolatedZeros(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Algebra_InfiniteSum_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_LSeries_RiemannZeta(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_LSeries_Nonvanishing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Filter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
