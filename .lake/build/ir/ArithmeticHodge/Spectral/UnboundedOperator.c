// Lean compiler output
// Module: ArithmeticHodge.Spectral.UnboundedOperator
// Imports: public import Init public import Mathlib.Analysis.InnerProductSpace.Basic public import Mathlib.Analysis.InnerProductSpace.Adjoint public import Mathlib.Analysis.InnerProductSpace.Continuous public import Mathlib.MeasureTheory.Function.L2Space public import Mathlib.Analysis.InnerProductSpace.Calculus public import Mathlib.Topology.MetricSpace.Basic public import Mathlib.Analysis.SpecialFunctions.Complex.Circle public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus public import Mathlib.Analysis.Calculus.Deriv.Slope public import Mathlib.Analysis.Calculus.MeanValue
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
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Adjoint(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Continuous(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Function_L2Space(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Calculus(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_MetricSpace_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Circle(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_FundThmCalculus(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Slope(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_MeanValue(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Spectral_UnboundedOperator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Adjoint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Continuous(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Function_L2Space(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Calculus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_MetricSpace_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Circle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_IntervalIntegral_FundThmCalculus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Slope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_MeanValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
