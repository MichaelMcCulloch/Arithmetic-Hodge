// Lean compiler output
// Module: ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct
// Imports: public import Init public import Mathlib.Analysis.SpecialFunctions.Complex.Log public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv public import Mathlib.Analysis.SpecialFunctions.ExpDeriv public import Mathlib.Analysis.Analytic.Basic public import Mathlib.Analysis.Analytic.IsolatedZeros public import Mathlib.Topology.Algebra.InfiniteSum.Basic public import Mathlib.Analysis.Normed.Field.Basic public import Mathlib.Analysis.SpecialFunctions.Pow.Complex public import Mathlib.Analysis.SpecialFunctions.Log.Summable public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic public import Mathlib.Analysis.Calculus.MeanValue public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn public import Mathlib.Analysis.Complex.LocallyUniformLimit
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
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_LogDeriv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_ExpDeriv(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Analytic_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Analytic_IsolatedZeros(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Algebra_InfiniteSum_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Field_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Complex(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Summable(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_NNReal(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Analytic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_MeanValue(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_FundThmCalculus(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Module_MultipliableUniformlyOn(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_LocallyUniformLimit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Weierstra_xdfProduct(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Log(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_LogDeriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_ExpDeriv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Analytic_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Analytic_IsolatedZeros(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Algebra_InfiniteSum_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Field_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Complex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Log_Summable(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_NNReal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Analytic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_MeanValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_FundThmCalculus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Module_MultipliableUniformlyOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_LocallyUniformLimit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
