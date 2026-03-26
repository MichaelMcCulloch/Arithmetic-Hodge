// Lean compiler output
// Module: ArithmeticHodge
// Imports: public import Init public import ArithmeticHodge.Algebra.DistributiveCoupling public import ArithmeticHodge.Analysis.PoissonSummation public import ArithmeticHodge.Analysis.ThetaFunction public import ArithmeticHodge.Analysis.ZetaFunctionalEquation public import ArithmeticHodge.Analysis.WeilDefs public import ArithmeticHodge.Analysis.EntireFunction.WeierstraßProduct public import ArithmeticHodge.Analysis.EntireFunction.Order public import ArithmeticHodge.Analysis.EntireFunction.Hadamard public import ArithmeticHodge.Analysis.ZetaProduct public import ArithmeticHodge.Analysis.WeilExplicit public import ArithmeticHodge.Analysis.FourierTransform public import ArithmeticHodge.Analysis.WeilPositivity public import ArithmeticHodge.Adelic.ClassSpace public import ArithmeticHodge.Adelic.SelbergUnfolding public import ArithmeticHodge.Adelic.TateLocalComputation public import ArithmeticHodge.Spectral.UnboundedOperator public import ArithmeticHodge.Spectral.SelfAdjointness public import ArithmeticHodge.Spectral.SpectralPositivity public import ArithmeticHodge.Spectral.ResolventComputation public import ArithmeticHodge.Spectral.TraceFormula public import ArithmeticHodge.Adelic.OrbitalIntegrals public import ArithmeticHodge.Arithmetic.HodgeIndex public import ArithmeticHodge.Strategy.DetailedBalance
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
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Algebra_DistributiveCoupling(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_PoissonSummation(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_ThetaFunction(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_ZetaFunctionalEquation(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilDefs(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Weierstra_xdfProduct(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Order(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Hadamard(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_ZetaProduct(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilExplicit(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_FourierTransform(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilPositivity(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Adelic_ClassSpace(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Adelic_SelbergUnfolding(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Adelic_TateLocalComputation(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Spectral_UnboundedOperator(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Spectral_SelfAdjointness(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Spectral_SpectralPositivity(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Spectral_ResolventComputation(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Spectral_TraceFormula(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Adelic_OrbitalIntegrals(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Arithmetic_HodgeIndex(uint8_t builtin);
lean_object* initialize_ArithmeticHodge_ArithmeticHodge_Strategy_DetailedBalance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_ArithmeticHodge_ArithmeticHodge(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Algebra_DistributiveCoupling(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_PoissonSummation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_ThetaFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_ZetaFunctionalEquation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilDefs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Weierstra_xdfProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_EntireFunction_Hadamard(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_ZetaProduct(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilExplicit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_FourierTransform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Analysis_WeilPositivity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Adelic_ClassSpace(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Adelic_SelbergUnfolding(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Adelic_TateLocalComputation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Spectral_UnboundedOperator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Spectral_SelfAdjointness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Spectral_SpectralPositivity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Spectral_ResolventComputation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Spectral_TraceFormula(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Adelic_OrbitalIntegrals(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Arithmetic_HodgeIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_ArithmeticHodge_ArithmeticHodge_Strategy_DetailedBalance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
