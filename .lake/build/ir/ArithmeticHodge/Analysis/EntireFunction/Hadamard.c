// Lean compiler output
// Module: ArithmeticHodge.Analysis.EntireFunction.Hadamard
// Imports: public import Init public import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct public import ArithmeticHodge.Analysis.EntireFunction.Order public import Mathlib.Analysis.Complex.BorelCaratheodory public import Mathlib.Analysis.Complex.AbsMax public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
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
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Weierstra_xdfProduct(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Order(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_BorelCaratheodory(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Complex_AbsMax(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_LogDerivUniformlyOn(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Hadamard(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Weierstra_xdfProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_BorelCaratheodory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Complex_AbsMax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_LogDerivUniformlyOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
