// Lean compiler output
// Module: ArithmeticHodge.Adelic.ClassSpace
// Imports: public import Init public import Mathlib.NumberTheory.NumberField.AdeleRing public import Mathlib.MeasureTheory.Measure.Haar.Basic public import Mathlib.Topology.Algebra.Group.Basic public import Mathlib.Analysis.SpecialFunctions.Pow.Real public import Mathlib.RingTheory.DedekindDomain.AdicValuation public import Mathlib.RingTheory.Int.Basic public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
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
lean_object* initialize_mathlib_Mathlib_NumberTheory_NumberField_AdeleRing(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Algebra_Group_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_DedekindDomain_AdicValuation(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_RingTheory_Int_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_MulEquivHaarChar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Adelic_ClassSpace(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_NumberTheory_NumberField_AdeleRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Algebra_Group_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Pow_Real(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_DedekindDomain_AdicValuation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_RingTheory_Int_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_MeasureTheory_Measure_Haar_MulEquivHaarChar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
