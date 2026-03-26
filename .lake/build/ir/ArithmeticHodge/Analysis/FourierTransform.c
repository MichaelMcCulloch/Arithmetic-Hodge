// Lean compiler output
// Module: ArithmeticHodge.Analysis.FourierTransform
// Imports: public import Init public import Mathlib.MeasureTheory.Integral.Bochner.Basic public import Mathlib.MeasureTheory.Function.L2Space public import Mathlib.Analysis.InnerProductSpace.Basic public import Mathlib.MeasureTheory.Group.Integral public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic public import ArithmeticHodge.Analysis.WeilExplicit
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
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Integral_Bochner_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Function_L2Space(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Group_Integral(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilExplicit(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_FourierTransform(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Integral_Bochner_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Function_L2Space(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_InnerProductSpace_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Group_Integral(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Trigonometric_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilExplicit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
