// Lean compiler output
// Module: ArithmeticHodge.Spectral.TraceFormula
// Imports: public import Init public import ArithmeticHodge.Spectral.SpectralPositivity public import ArithmeticHodge.Adelic.OrbitalIntegrals public import ArithmeticHodge.Analysis.WeilPositivity
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
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Spectral_SpectralPositivity(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Adelic_OrbitalIntegrals(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilPositivity(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Spectral_TraceFormula(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Spectral_SpectralPositivity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Adelic_OrbitalIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilPositivity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
