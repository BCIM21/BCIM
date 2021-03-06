// Generated by using Rcpp::compileAttributes() -> do not edit by hand
// Generator token: 10BE3573-1514-4C36-9D1C-5A225CD40393

#include <RcppArmadillo.h>
#include <Rcpp.h>

using namespace Rcpp;

// rcpparma_hello_world
arma::mat rcpparma_hello_world();
RcppExport SEXP _BCEndo_rcpparma_hello_world() {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    rcpp_result_gen = Rcpp::wrap(rcpparma_hello_world());
    return rcpp_result_gen;
END_RCPP
}
// rcpparma_outerproduct
arma::mat rcpparma_outerproduct(const arma::colvec& x);
RcppExport SEXP _BCEndo_rcpparma_outerproduct(SEXP xSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const arma::colvec& >::type x(xSEXP);
    rcpp_result_gen = Rcpp::wrap(rcpparma_outerproduct(x));
    return rcpp_result_gen;
END_RCPP
}
// rcpparma_innerproduct
double rcpparma_innerproduct(const arma::colvec& x);
RcppExport SEXP _BCEndo_rcpparma_innerproduct(SEXP xSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const arma::colvec& >::type x(xSEXP);
    rcpp_result_gen = Rcpp::wrap(rcpparma_innerproduct(x));
    return rcpp_result_gen;
END_RCPP
}
// rcpparma_bothproducts
Rcpp::List rcpparma_bothproducts(const arma::colvec& x);
RcppExport SEXP _BCEndo_rcpparma_bothproducts(SEXP xSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const arma::colvec& >::type x(xSEXP);
    rcpp_result_gen = Rcpp::wrap(rcpparma_bothproducts(x));
    return rcpp_result_gen;
END_RCPP
}
// DF2mat
NumericMatrix DF2mat(DataFrame x);
RcppExport SEXP _BCEndo_DF2mat(SEXP xSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< DataFrame >::type x(xSEXP);
    rcpp_result_gen = Rcpp::wrap(DF2mat(x));
    return rcpp_result_gen;
END_RCPP
}
// draw_regcoef_cpp
arma::vec draw_regcoef_cpp(arma::mat y, arma::mat X, double sigma2, arma::mat B0);
RcppExport SEXP _BCEndo_draw_regcoef_cpp(SEXP ySEXP, SEXP XSEXP, SEXP sigma2SEXP, SEXP B0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< arma::mat >::type y(ySEXP);
    Rcpp::traits::input_parameter< arma::mat >::type X(XSEXP);
    Rcpp::traits::input_parameter< double >::type sigma2(sigma2SEXP);
    Rcpp::traits::input_parameter< arma::mat >::type B0(B0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_regcoef_cpp(y, X, sigma2, B0));
    return rcpp_result_gen;
END_RCPP
}
// draw_regcoef_overparam_cpp
arma::vec draw_regcoef_overparam_cpp(arma::mat y, arma::mat X, double sigma2, arma::mat b0, arma::mat B0);
RcppExport SEXP _BCEndo_draw_regcoef_overparam_cpp(SEXP ySEXP, SEXP XSEXP, SEXP sigma2SEXP, SEXP b0SEXP, SEXP B0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< arma::mat >::type y(ySEXP);
    Rcpp::traits::input_parameter< arma::mat >::type X(XSEXP);
    Rcpp::traits::input_parameter< double >::type sigma2(sigma2SEXP);
    Rcpp::traits::input_parameter< arma::mat >::type b0(b0SEXP);
    Rcpp::traits::input_parameter< arma::mat >::type B0(B0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_regcoef_overparam_cpp(y, X, sigma2, b0, B0));
    return rcpp_result_gen;
END_RCPP
}
// ffbs_cpp
arma::mat ffbs_cpp(arma::mat m0, arma::mat C0, arma::mat Y, arma::cube F, arma::mat G, arma::mat V, arma::mat W, double N, double TT);
RcppExport SEXP _BCEndo_ffbs_cpp(SEXP m0SEXP, SEXP C0SEXP, SEXP YSEXP, SEXP FSEXP, SEXP GSEXP, SEXP VSEXP, SEXP WSEXP, SEXP NSEXP, SEXP TTSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< arma::mat >::type m0(m0SEXP);
    Rcpp::traits::input_parameter< arma::mat >::type C0(C0SEXP);
    Rcpp::traits::input_parameter< arma::mat >::type Y(YSEXP);
    Rcpp::traits::input_parameter< arma::cube >::type F(FSEXP);
    Rcpp::traits::input_parameter< arma::mat >::type G(GSEXP);
    Rcpp::traits::input_parameter< arma::mat >::type V(VSEXP);
    Rcpp::traits::input_parameter< arma::mat >::type W(WSEXP);
    Rcpp::traits::input_parameter< double >::type N(NSEXP);
    Rcpp::traits::input_parameter< double >::type TT(TTSEXP);
    rcpp_result_gen = Rcpp::wrap(ffbs_cpp(m0, C0, Y, F, G, V, W, N, TT));
    return rcpp_result_gen;
END_RCPP
}
// horseshoe_cpp
List horseshoe_cpp(arma::mat y, arma::mat X, double Sigma2, double tau, arma::vec lambda);
RcppExport SEXP _BCEndo_horseshoe_cpp(SEXP ySEXP, SEXP XSEXP, SEXP Sigma2SEXP, SEXP tauSEXP, SEXP lambdaSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< arma::mat >::type y(ySEXP);
    Rcpp::traits::input_parameter< arma::mat >::type X(XSEXP);
    Rcpp::traits::input_parameter< double >::type Sigma2(Sigma2SEXP);
    Rcpp::traits::input_parameter< double >::type tau(tauSEXP);
    Rcpp::traits::input_parameter< arma::vec >::type lambda(lambdaSEXP);
    rcpp_result_gen = Rcpp::wrap(horseshoe_cpp(y, X, Sigma2, tau, lambda));
    return rcpp_result_gen;
END_RCPP
}
// draw_beta_p0_l_cpp
arma::mat draw_beta_p0_l_cpp(const List datP, List paramp);
RcppExport SEXP _BCEndo_draw_beta_p0_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_beta_p0_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_individual_intercept_p0_i_l_overparam_cpp
List draw_individual_intercept_p0_i_l_overparam_cpp(const List datP, List paramp);
RcppExport SEXP _BCEndo_draw_individual_intercept_p0_i_l_overparam_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_individual_intercept_p0_i_l_overparam_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_alpha_p0_i_l_overparam_cpp
List draw_alpha_p0_i_l_overparam_cpp(const List datP, List paramp);
RcppExport SEXP _BCEndo_draw_alpha_p0_i_l_overparam_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_alpha_p0_i_l_overparam_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_alpha_p0_i_l_overparam_with_intercept_cpp
List draw_alpha_p0_i_l_overparam_with_intercept_cpp(const List datP, List paramp);
RcppExport SEXP _BCEndo_draw_alpha_p0_i_l_overparam_with_intercept_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_alpha_p0_i_l_overparam_with_intercept_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_gamma_p0_i_l_cpp
arma::mat draw_gamma_p0_i_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_gamma_p0_i_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_gamma_p0_i_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_gamma_p0_i_l_hs_cpp
List draw_gamma_p0_i_l_hs_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_gamma_p0_i_l_hs_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_gamma_p0_i_l_hs_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_xi_f_p0_t_l_cpp
List draw_xi_f_p0_t_l_cpp(List dataP, List paramp0);
RcppExport SEXP _BCEndo_draw_xi_f_p0_t_l_cpp(SEXP dataPSEXP, SEXP paramp0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataP(dataPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp0(paramp0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_xi_f_p0_t_l_cpp(dataP, paramp0));
    return rcpp_result_gen;
END_RCPP
}
// draw_xi_p0_t_l_with_intercept_cpp
arma::mat draw_xi_p0_t_l_with_intercept_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_xi_p0_t_l_with_intercept_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_xi_p0_t_l_with_intercept_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_xi_p0_t_l_intercept_only_cpp
arma::mat draw_xi_p0_t_l_intercept_only_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_xi_p0_t_l_intercept_only_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_xi_p0_t_l_intercept_only_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_xi_p0_t_l_cpp
arma::mat draw_xi_p0_t_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_xi_p0_t_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_xi_p0_t_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_f_p0_t_l_cpp
arma::mat draw_f_p0_t_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_f_p0_t_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_f_p0_t_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_phi_xi_p0_j_l_cpp
List draw_phi_xi_p0_j_l_cpp(List dataP, List paramp0);
RcppExport SEXP _BCEndo_draw_phi_xi_p0_j_l_cpp(SEXP dataPSEXP, SEXP paramp0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataP(dataPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp0(paramp0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_phi_xi_p0_j_l_cpp(dataP, paramp0));
    return rcpp_result_gen;
END_RCPP
}
// draw_phi_f_p0_j_l_cpp
arma::mat draw_phi_f_p0_j_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_phi_f_p0_j_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_phi_f_p0_j_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_sigma2_e_p0_j_l_cpp
arma::mat draw_sigma2_e_p0_j_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_sigma2_e_p0_j_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_sigma2_e_p0_j_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_sigma2_eps_p0_l_cpp
double draw_sigma2_eps_p0_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_sigma2_eps_p0_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_sigma2_eps_p0_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_pi_p0_j_l_cpp
List draw_pi_p0_j_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_pi_p0_j_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_pi_p0_j_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_theta_p0_l_cpp
double draw_theta_p0_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_theta_p0_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_theta_p0_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_tau2_p0_l_cpp
double draw_tau2_p0_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_tau2_p0_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_tau2_p0_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_s_p0_l_cpp
double draw_s_p0_l_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_s_p0_l_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_s_p0_l_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_p0_mis_cpp
arma::vec draw_p0_mis_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_p0_mis_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_p0_mis_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_p0_delta_cpp
arma::vec draw_p0_delta_cpp(List datP, List paramp);
RcppExport SEXP _BCEndo_draw_p0_delta_cpp(SEXP datPSEXP, SEXP parampSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type datP(datPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp(parampSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_p0_delta_cpp(datP, paramp));
    return rcpp_result_gen;
END_RCPP
}
// draw_phi_delta_p_cpp
List draw_phi_delta_p_cpp(List dataP, List paramp0, int addTimeTreandforDelta);
RcppExport SEXP _BCEndo_draw_phi_delta_p_cpp(SEXP dataPSEXP, SEXP paramp0SEXP, SEXP addTimeTreandforDeltaSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataP(dataPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp0(paramp0SEXP);
    Rcpp::traits::input_parameter< int >::type addTimeTreandforDelta(addTimeTreandforDeltaSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_phi_delta_p_cpp(dataP, paramp0, addTimeTreandforDelta));
    return rcpp_result_gen;
END_RCPP
}
// draw_sigma2_eta_p_cpp
List draw_sigma2_eta_p_cpp(List dataP, List paramp0, int addTimeTreandforDelta);
RcppExport SEXP _BCEndo_draw_sigma2_eta_p_cpp(SEXP dataPSEXP, SEXP paramp0SEXP, SEXP addTimeTreandforDeltaSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataP(dataPSEXP);
    Rcpp::traits::input_parameter< List >::type paramp0(paramp0SEXP);
    Rcpp::traits::input_parameter< int >::type addTimeTreandforDelta(addTimeTreandforDeltaSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_sigma2_eta_p_cpp(dataP, paramp0, addTimeTreandforDelta));
    return rcpp_result_gen;
END_RCPP
}
// draw_beta_y0_cpp
List draw_beta_y0_cpp(const List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_beta_y0_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_beta_y0_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_individual_intercept_y0_overparam_cpp
List draw_individual_intercept_y0_overparam_cpp(const List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_individual_intercept_y0_overparam_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_individual_intercept_y0_overparam_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_alpha_y0_i_overparam_cpp
List draw_alpha_y0_i_overparam_cpp(const List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_alpha_y0_i_overparam_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_alpha_y0_i_overparam_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_alpha_y0_i_overparam_with_intercept_cpp
List draw_alpha_y0_i_overparam_with_intercept_cpp(const List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_alpha_y0_i_overparam_with_intercept_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< const List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_alpha_y0_i_overparam_with_intercept_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_gamma_y0_i_cpp
List draw_gamma_y0_i_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_gamma_y0_i_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_gamma_y0_i_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_gamma_y0_i_hs_cpp
List draw_gamma_y0_i_hs_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_gamma_y0_i_hs_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_gamma_y0_i_hs_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_xi_f_y0_t_cpp
List draw_xi_f_y0_t_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_xi_f_y0_t_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_xi_f_y0_t_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_xi_y0_t_with_intercept_cpp
List draw_xi_y0_t_with_intercept_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_xi_y0_t_with_intercept_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_xi_y0_t_with_intercept_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_xi_y0_t_intercept_only_cpp
List draw_xi_y0_t_intercept_only_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_xi_y0_t_intercept_only_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_xi_y0_t_intercept_only_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_xi_y0_t_cpp
List draw_xi_y0_t_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_xi_y0_t_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_xi_y0_t_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_f_y0_t_cpp
List draw_f_y0_t_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_f_y0_t_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_f_y0_t_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_phi_xi_y0_j_cpp
List draw_phi_xi_y0_j_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_phi_xi_y0_j_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_phi_xi_y0_j_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_phi_f_y0_j_cpp
List draw_phi_f_y0_j_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_phi_f_y0_j_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_phi_f_y0_j_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_sigma2_e_y0_j_cpp
List draw_sigma2_e_y0_j_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_sigma2_e_y0_j_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_sigma2_e_y0_j_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_sigma2_eps_y0_cpp
List draw_sigma2_eps_y0_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_sigma2_eps_y0_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_sigma2_eps_y0_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_pi_y0_j_cpp
List draw_pi_y0_j_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_pi_y0_j_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_pi_y0_j_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_theta_y0_cpp
List draw_theta_y0_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_theta_y0_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_theta_y0_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_tau2_y0_cpp
List draw_tau2_y0_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_tau2_y0_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_tau2_y0_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_s_y0_cpp
List draw_s_y0_cpp(List dataY, List paramy0);
RcppExport SEXP _BCEndo_draw_s_y0_cpp(SEXP dataYSEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_s_y0_cpp(dataY, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_y0_mis_cpp
List draw_y0_mis_cpp(List dataY, List paramp0, List paramy0);
RcppExport SEXP _BCEndo_draw_y0_mis_cpp(SEXP dataYSEXP, SEXP paramp0SEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramp0(paramp0SEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_y0_mis_cpp(dataY, paramp0, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_y0_delta_cpp
List draw_y0_delta_cpp(List dataY, List paramp0, List paramy0);
RcppExport SEXP _BCEndo_draw_y0_delta_cpp(SEXP dataYSEXP, SEXP paramp0SEXP, SEXP paramy0SEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramp0(paramp0SEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    rcpp_result_gen = Rcpp::wrap(draw_y0_delta_cpp(dataY, paramp0, paramy0));
    return rcpp_result_gen;
END_RCPP
}
// draw_phi_delta_y_cpp
List draw_phi_delta_y_cpp(List dataY, List paramy0, int addTimeTreandforDelta);
RcppExport SEXP _BCEndo_draw_phi_delta_y_cpp(SEXP dataYSEXP, SEXP paramy0SEXP, SEXP addTimeTreandforDeltaSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    Rcpp::traits::input_parameter< int >::type addTimeTreandforDelta(addTimeTreandforDeltaSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_phi_delta_y_cpp(dataY, paramy0, addTimeTreandforDelta));
    return rcpp_result_gen;
END_RCPP
}
// draw_sigma2_eta_y_cpp
List draw_sigma2_eta_y_cpp(List dataY, List paramy0, int addTimeTreandforDelta);
RcppExport SEXP _BCEndo_draw_sigma2_eta_y_cpp(SEXP dataYSEXP, SEXP paramy0SEXP, SEXP addTimeTreandforDeltaSEXP) {
BEGIN_RCPP
    Rcpp::RObject rcpp_result_gen;
    Rcpp::RNGScope rcpp_rngScope_gen;
    Rcpp::traits::input_parameter< List >::type dataY(dataYSEXP);
    Rcpp::traits::input_parameter< List >::type paramy0(paramy0SEXP);
    Rcpp::traits::input_parameter< int >::type addTimeTreandforDelta(addTimeTreandforDeltaSEXP);
    rcpp_result_gen = Rcpp::wrap(draw_sigma2_eta_y_cpp(dataY, paramy0, addTimeTreandforDelta));
    return rcpp_result_gen;
END_RCPP
}

static const R_CallMethodDef CallEntries[] = {
    {"_BCEndo_rcpparma_hello_world", (DL_FUNC) &_BCEndo_rcpparma_hello_world, 0},
    {"_BCEndo_rcpparma_outerproduct", (DL_FUNC) &_BCEndo_rcpparma_outerproduct, 1},
    {"_BCEndo_rcpparma_innerproduct", (DL_FUNC) &_BCEndo_rcpparma_innerproduct, 1},
    {"_BCEndo_rcpparma_bothproducts", (DL_FUNC) &_BCEndo_rcpparma_bothproducts, 1},
    {"_BCEndo_DF2mat", (DL_FUNC) &_BCEndo_DF2mat, 1},
    {"_BCEndo_draw_regcoef_cpp", (DL_FUNC) &_BCEndo_draw_regcoef_cpp, 4},
    {"_BCEndo_draw_regcoef_overparam_cpp", (DL_FUNC) &_BCEndo_draw_regcoef_overparam_cpp, 5},
    {"_BCEndo_ffbs_cpp", (DL_FUNC) &_BCEndo_ffbs_cpp, 9},
    {"_BCEndo_horseshoe_cpp", (DL_FUNC) &_BCEndo_horseshoe_cpp, 5},
    {"_BCEndo_draw_beta_p0_l_cpp", (DL_FUNC) &_BCEndo_draw_beta_p0_l_cpp, 2},
    {"_BCEndo_draw_individual_intercept_p0_i_l_overparam_cpp", (DL_FUNC) &_BCEndo_draw_individual_intercept_p0_i_l_overparam_cpp, 2},
    {"_BCEndo_draw_alpha_p0_i_l_overparam_cpp", (DL_FUNC) &_BCEndo_draw_alpha_p0_i_l_overparam_cpp, 2},
    {"_BCEndo_draw_alpha_p0_i_l_overparam_with_intercept_cpp", (DL_FUNC) &_BCEndo_draw_alpha_p0_i_l_overparam_with_intercept_cpp, 2},
    {"_BCEndo_draw_gamma_p0_i_l_cpp", (DL_FUNC) &_BCEndo_draw_gamma_p0_i_l_cpp, 2},
    {"_BCEndo_draw_gamma_p0_i_l_hs_cpp", (DL_FUNC) &_BCEndo_draw_gamma_p0_i_l_hs_cpp, 2},
    {"_BCEndo_draw_xi_f_p0_t_l_cpp", (DL_FUNC) &_BCEndo_draw_xi_f_p0_t_l_cpp, 2},
    {"_BCEndo_draw_xi_p0_t_l_with_intercept_cpp", (DL_FUNC) &_BCEndo_draw_xi_p0_t_l_with_intercept_cpp, 2},
    {"_BCEndo_draw_xi_p0_t_l_intercept_only_cpp", (DL_FUNC) &_BCEndo_draw_xi_p0_t_l_intercept_only_cpp, 2},
    {"_BCEndo_draw_xi_p0_t_l_cpp", (DL_FUNC) &_BCEndo_draw_xi_p0_t_l_cpp, 2},
    {"_BCEndo_draw_f_p0_t_l_cpp", (DL_FUNC) &_BCEndo_draw_f_p0_t_l_cpp, 2},
    {"_BCEndo_draw_phi_xi_p0_j_l_cpp", (DL_FUNC) &_BCEndo_draw_phi_xi_p0_j_l_cpp, 2},
    {"_BCEndo_draw_phi_f_p0_j_l_cpp", (DL_FUNC) &_BCEndo_draw_phi_f_p0_j_l_cpp, 2},
    {"_BCEndo_draw_sigma2_e_p0_j_l_cpp", (DL_FUNC) &_BCEndo_draw_sigma2_e_p0_j_l_cpp, 2},
    {"_BCEndo_draw_sigma2_eps_p0_l_cpp", (DL_FUNC) &_BCEndo_draw_sigma2_eps_p0_l_cpp, 2},
    {"_BCEndo_draw_pi_p0_j_l_cpp", (DL_FUNC) &_BCEndo_draw_pi_p0_j_l_cpp, 2},
    {"_BCEndo_draw_theta_p0_l_cpp", (DL_FUNC) &_BCEndo_draw_theta_p0_l_cpp, 2},
    {"_BCEndo_draw_tau2_p0_l_cpp", (DL_FUNC) &_BCEndo_draw_tau2_p0_l_cpp, 2},
    {"_BCEndo_draw_s_p0_l_cpp", (DL_FUNC) &_BCEndo_draw_s_p0_l_cpp, 2},
    {"_BCEndo_draw_p0_mis_cpp", (DL_FUNC) &_BCEndo_draw_p0_mis_cpp, 2},
    {"_BCEndo_draw_p0_delta_cpp", (DL_FUNC) &_BCEndo_draw_p0_delta_cpp, 2},
    {"_BCEndo_draw_phi_delta_p_cpp", (DL_FUNC) &_BCEndo_draw_phi_delta_p_cpp, 3},
    {"_BCEndo_draw_sigma2_eta_p_cpp", (DL_FUNC) &_BCEndo_draw_sigma2_eta_p_cpp, 3},
    {"_BCEndo_draw_beta_y0_cpp", (DL_FUNC) &_BCEndo_draw_beta_y0_cpp, 2},
    {"_BCEndo_draw_individual_intercept_y0_overparam_cpp", (DL_FUNC) &_BCEndo_draw_individual_intercept_y0_overparam_cpp, 2},
    {"_BCEndo_draw_alpha_y0_i_overparam_cpp", (DL_FUNC) &_BCEndo_draw_alpha_y0_i_overparam_cpp, 2},
    {"_BCEndo_draw_alpha_y0_i_overparam_with_intercept_cpp", (DL_FUNC) &_BCEndo_draw_alpha_y0_i_overparam_with_intercept_cpp, 2},
    {"_BCEndo_draw_gamma_y0_i_cpp", (DL_FUNC) &_BCEndo_draw_gamma_y0_i_cpp, 2},
    {"_BCEndo_draw_gamma_y0_i_hs_cpp", (DL_FUNC) &_BCEndo_draw_gamma_y0_i_hs_cpp, 2},
    {"_BCEndo_draw_xi_f_y0_t_cpp", (DL_FUNC) &_BCEndo_draw_xi_f_y0_t_cpp, 2},
    {"_BCEndo_draw_xi_y0_t_with_intercept_cpp", (DL_FUNC) &_BCEndo_draw_xi_y0_t_with_intercept_cpp, 2},
    {"_BCEndo_draw_xi_y0_t_intercept_only_cpp", (DL_FUNC) &_BCEndo_draw_xi_y0_t_intercept_only_cpp, 2},
    {"_BCEndo_draw_xi_y0_t_cpp", (DL_FUNC) &_BCEndo_draw_xi_y0_t_cpp, 2},
    {"_BCEndo_draw_f_y0_t_cpp", (DL_FUNC) &_BCEndo_draw_f_y0_t_cpp, 2},
    {"_BCEndo_draw_phi_xi_y0_j_cpp", (DL_FUNC) &_BCEndo_draw_phi_xi_y0_j_cpp, 2},
    {"_BCEndo_draw_phi_f_y0_j_cpp", (DL_FUNC) &_BCEndo_draw_phi_f_y0_j_cpp, 2},
    {"_BCEndo_draw_sigma2_e_y0_j_cpp", (DL_FUNC) &_BCEndo_draw_sigma2_e_y0_j_cpp, 2},
    {"_BCEndo_draw_sigma2_eps_y0_cpp", (DL_FUNC) &_BCEndo_draw_sigma2_eps_y0_cpp, 2},
    {"_BCEndo_draw_pi_y0_j_cpp", (DL_FUNC) &_BCEndo_draw_pi_y0_j_cpp, 2},
    {"_BCEndo_draw_theta_y0_cpp", (DL_FUNC) &_BCEndo_draw_theta_y0_cpp, 2},
    {"_BCEndo_draw_tau2_y0_cpp", (DL_FUNC) &_BCEndo_draw_tau2_y0_cpp, 2},
    {"_BCEndo_draw_s_y0_cpp", (DL_FUNC) &_BCEndo_draw_s_y0_cpp, 2},
    {"_BCEndo_draw_y0_mis_cpp", (DL_FUNC) &_BCEndo_draw_y0_mis_cpp, 3},
    {"_BCEndo_draw_y0_delta_cpp", (DL_FUNC) &_BCEndo_draw_y0_delta_cpp, 3},
    {"_BCEndo_draw_phi_delta_y_cpp", (DL_FUNC) &_BCEndo_draw_phi_delta_y_cpp, 3},
    {"_BCEndo_draw_sigma2_eta_y_cpp", (DL_FUNC) &_BCEndo_draw_sigma2_eta_y_cpp, 3},
    {NULL, NULL, 0}
};

RcppExport void R_init_BCEndo(DllInfo *dll) {
    R_registerRoutines(dll, NULL, CallEntries, NULL, NULL);
    R_useDynamicSymbols(dll, FALSE);
}
