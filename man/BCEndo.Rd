\name{BCEndo}
\alias{BCEndo}
\title{BCEndo}
\description{Estimate the BCEndo model}
\usage{BCEndo(data, index, OutcomeEqInfo, MediatorEqInfo, NBURN, THIN, NCOLLECT)}

\arguments{
\item{data}{A data frame that contains an estimaton data set of N units over TT periods. See Details.}
\item{index}{A character vector of length 2. The first element is the name of the variable that identifies units in data, the second element is the name of the variable that identifies period in data}
\item{OutcomeEqInfo}{A list that contains the outcome equation information. BCEndo uses the information in this list to estimate the Outcome Equation. See Details.}
\item{MediatorEqInfo}{A list that contains the mediator equation information. BCEndo uses the information in this list to estimate the Mediator Equation. See Details.}
\item{NBURN}{number of burn-in iterations in the MCMC algorithm}
\item{THIN}{the thinning parameter}
\item{NCOLLECT}{number of samples to collect after burnin. After burnin, each THIN_th sample is saved.}
}


\details{

  \code{data} is a data frame that contains the data to be used to estiamte the causal treatment effect. Check the accompanying data file in the package by typing \code{data(df_eligible)} and \code{?df_eligible} to understand the variables need to be included in the data frame.
  
  \code{OutcomeEqInfo} is a list that contains following information for the estimation of the Outcome  Equation. 
  \itemize{
    \item $Y: the outcome variable in data
    \item $D: the treatment indicator (1 or 0) in \code{data}
    \item $Xp: mediators in \code{data}. In case of no mediators, \code{Xp = NULL}.
    \item $Xq: exogenous covariates in \code{data}. Do not add an intercept; it is added automatically by the program.
    \item $Xdelta: variables that explain the direct treatment effect. Do not add an intercept. It is added automatically by the program. 
    \item $treat: identifier of treatment units (1 or 0) in \code{data}
    \item $nFactor :number of latent factors
    \item $re: random effect specification for the intercept ("none", "unit", "time", or "both")
    \item $estimate_individual_coefs: whether to estimate unit-specific coefficients (1 or 0)
    \item $estimate_time_varying_coefs: whether to estimate time-varying coefficients (1 or 0)
    \item $estimate_phi_delta: whether to conduct a moderation analysis for the direct treatment effects (1 or 0)
    \item $factor_selection_method: methods to select latent factors ("horseshoe" or "spike-slab")
  }
  
  
  \code{MediatorEqInfo} is a list that contains following information for the estimation of k_y1 Mediator Equations. \code{MediatorEqInfo = NULL} if \code{OutcomeEqInfo$Xp = NULL}. 
  \itemize{
    \item $P: the variables in \code{data} that correspond to mediators. A list of length k_y1. \code{$P = as.list(OutcomeEqInfo$Xp)} by definition.
    \item $X: covariates of the mediator equations. A list of length k_y1 where each element is a vector that contains covariates of each mediator equation. Do not add an intercept; it is added automatically by the program.
    \item $Xdelta: covarates of the moderator equations that explain the treatment's effects on the mediators. A list of length k_y1 where each element is a vector that contatins covariates for the moderation analysis of each mediation equation.
    \item $nFactor: number of latent factors. A vector of length k_y1.
    \item $re: random effect specification for the intercept of each mediator equation ("none", "unit", "time", or "both"). A vector of length k_y1.
    \item $estimate_individual_coefs: whether to estimate unit-specific coefficients (1 or 0). A vector of length k_y1.
    \item $estimate_time_varying_coefs: whether to estimate time-varying coefficients (1 or 0). A vector of length k_y1.
    \item $impute_p0_mis: whether to impute the counterfacual potential p0 under no treatment (1 or 0). A vector of length k_y1.
    \item $estimate_phi_delta: whether to conduct a moderation analysis for the treatment's effect on each mediator (1 or 0). A vector of length k_y1.
    \item $factor_selection_method: methods to select latent factors  ("horseshoe" or "spike-slab"). A vector of length k_y1. 
  }
}

\value{
  \code{BCEndo()} returns a list that contains the following elements.
  \itemize{
  \item dataP: the data used in the estimation of the Mediator Equations. It is extracted from \code{MediatorEqInfo} and \code{data}. In case of no mediators, \code{dataP} is not returned.
  \item dataY: the data used in the estimation of the Outcome Equation. It is extracted from \code{OutcomeEqInfo} and \code{data}.
  \item MCMC_P: A list that contains the MCMC draws of the k_y1 Mediator Equations. It consists of the following elements.  In case of no mediators, \code{MCMC_P} is not returned.
  \itemize{
     \item $beta: A list of length k_y1. The l_th element is a data frame of size (NCOLLECT by the number of covariates and intercept of the l_th mediator equation) that saves the MCMC draws for betas (the population-level coefficients) of the l_th mediator equation. The last column of the data frame is the MCMC draws for the intercept.
     \item $alpha_i: A list of length k_y1. The l_th element is a 3D array of size (N by number of covariates and intercept of the l_th mediator equation by NCOLLECT) that saves the MCMC draws for alpha_i's (the unit-level coefficients) of the l_th mediator equation. The last column of the data frame is the MCMC draws for the intercept. 
     \item $xi: A list of length k_y1. The l_th element is a 3D array of size (TT by number of covariates and intercept of the l_th mediator equation by NCOLLECT) that saves the MCMC draws for x_t's (the time-varying coefficients) of the l_th mediator equation. The last column of the data frame is the MCMC draws for the intercept.
     \item $f: A list of length k_y1. The l_th element is a 3D array of size (TT by number of latent factors of the l_th mediator equation by NCOLLECT) that saves the MCMC draws for f_t's (the latent factors) of the l_th mediator equation.  
     \item $gamma_i:A list of length k_y1. The l_th element is a 3D array of size (N by number of factors of the l_th mediator equation by NCOLLECT) that saves the MCMC draws for gamma_i's (the factor loading on unit i) of the l_th mediator equation. 
     \item $phi_f: A list of length k_y1. The l_th element is a 3D array of size (TT by number of latent factors of the l_th mediator equation by NCOLLECT) that saves the MCMC draws for the autocorrelation coefficients of the latent factors of the l_th mediator equation.  
     \item $sigma2_e: A list of length k_y1. The l_th element is a data frame of size (NCOLLECT by number of covariates of the l_th mediator equation) that saves the MCMC draws for var(xi_(p,tl)), the variance of the time-varying coefficient (xi_t), of l_th mediator equation. 
     \item $sigma2_eps: A list of length k_y1. The l_th element is a vector of length NCOLLECT that saves the MCMC draws for var(epsilon_(p,itl)), the variance of the error term of l_th mediator equation. 
     \item $mu_alpha: A list of length k_y1. The l_th element is a data frame of size (NCOLLECT by the number of covariates of the l_th mediator equation) that saves the MCMC draws for mu_alphas, the mean of alpha_i's, of the l_th mediator equation.
     \item $delta: A list of length k_y1. The l_th element is a data frame of size (NCOLLECT by N*TT) that saves the MCMC draws for the treatment effect on the l_th mediator.
     \item $phi_delta: A list of length k_y1. The l_th element is a data frame of size (NCOLLECT by number of moderators for the l_th mediator equation) that saves the coefficients of the moderators. The last column of the data frame is the MCMC draws for the intercept.
     \item $sigma2_eta: A list of length k_y1. The l_th element is a vector of length NCOLLECT that saves the variance of the error term of the moderator equation for the l_th mediator equation.
     \item $p0_mis: A list of length k_y1. The l_th element is a data frame of size (NCOLLECT by N*TT) that saves the MCMC draws for p0_mis (the counterfactaul mediator values under treatment --i.e., the values that have been oberved if the unit had not adopted the treatment) of the l_th mediator.
     \item $factor_selection_method: A character vector of length k_y1 that saves the factor selection method (spike-slab or horseshoe) of the l_th mediator equation.
     \item $pi: A list of length k_y1. The l_th element is a data frame of size (NCOLLECT by number of latent factors of the l_th mediator equation) that saves the MCMC draws for the inclusion indicators (pi's) of the latent factors of the l_th mediator equation when spike-and-slab prior is used.
     \item $theta: A list of length k_y1. The l_th element is a vector of length NCOLLECT that saves the MCMC draws for the inclusion probabilities (theta's) of the latent factors of the l_th mediator equation when spike-and-slap prior is used.
     \item $tau2: A list of length k_y1 that saves MCMC draws for tau2, one of the parameters of the spike-slab prior.
     \item $s: A list of length k_y1 that saves MCMC draws for s, one of the parameters of the spike-slab prior. 
     \item $tau: A list of length k_y1 that saves MCMC draws for the parameter tau of the horseshoe prior. 
     \item $lambda: A list of length k_y1 that saves MCMC draws for the parameter lambda of the horseshoe prior.
  }
  
  \item MCMC_Y: A list that contains the MCMC draws of the Outcome Equation. It consists of the following elements. 
  \itemize{
    \item $beta: A data frame of size (NCOLLECT by number of covariates and intercept) that saves MCMC draws for the population-level coefficient (beta) in the outcome equation. The last column is the coefficient of the intercept. The last column of the data frame is the MCMC draws for the intercept.
    \item $alpha_i: A 3D array of size (N by number of covariates and intercept by NCOLLECT) that saves MCMC draws for the unit-level coefficient (alpha_i) in the outcome equation.  The last column of dimensin 2 is the coefficient of the intercept. The last column of the data frame is the MCMC draws for the intercept.
     \item $xi: A 3D array of size (TT by number of covariates and intercept by NCOLLECT) that saves MCMC draws for the time-varying coefficient (xi_t) in the outcome equation. The last column of dimensin 2 is the coefficient of the intercept. The last column of the data frame is the MCMC draws for the intercept.
     \item $f: A 3D array of size (TT by number of latent factors by NCOLLECT) that saves MCMC draws for the latent factors (f_t) in the outcome equation. 
     \item $gamma_i: A 3D array of size (N by number of latent factors by NCOLLECT) that saves MCMC draws for the unit-level factor loadings (gamma_i) in the outcome equation.
     \item $phi_f: A data frame of size (NCOLLECT by number of covariates and intercept) that saves MCMC draws for the autocorrelation coefficients of the latent factors (f_t) in the outcome equation.
     \item $sigma2_e: A data frame of size (NCOLLECT by number of covariates and intercept) that saves MCMC draws for the variance of the time-varying coefficient (xi_t) in the outcome equation. 
     \item $sigma2_eps: A vector of length NCOLLECT that saves MCMC draws for the variance of the error term of the outcome equation. 
     \item $mu_alpha: A data frame of size (NCOLLECT by number of covariates and intercept) that saves MCMC draws for mu_alpha, the mean of alpha_i, of the outcome equation. The last column is the coefficient of the intercept.
     \item $y0_mis: A data frame of size (NCOLLECT by N*TT) that saves the counterfactaul outcome values under treatment (i.e., the values that have been oberved if the unit had not adopted the treatment). 
     \item $tte: A data frame of size (NCOLLECT by N*TT) that saves the total effect of treatment on the outcome.
     \item $delta: A data frame of size (NCOLLECT by N*TT) that saves the direct effect of treatment on the outcome.
     \item $mte: A data frame of size (NCOLLECT by N*TT) that saves the mediated effect of treatment on the outcome.
     \item $phi_delta: A data frame of size (NCOLLECT by number of moderators of direct effect) that saves the coefficients of the moderators in the outcome equation. The last column of the data frame is the MCMC draws for the intercept.
     \item $sigma2_eta: A vector of length NCOLLECT that saves the variance of the error term of the moderator equation for the direct treatment effect.
     \item $factor_selection_method: A character vector of length 1 that saves the factor selection method (spike-slab or horseshoe) of the outcome equation.
     \item $pi: A data frame of size (NCOLLECT by latent factors) that saves MCMC draws for the inclusion indicator pi (1 or 0) of the latent factors of the outcome equation when spike-and-slab prior is used.
     \item $theta: A vector of length NCOLLECT that saves MCMC draws for the inclusion probability theta of the latent factors of the outcome equation when spike-and-slab prior is used.
     \item $tau2: A vector of length NCOLLECT that saves MCMC draws for tau2, one of the parameters of the spike-slab prior.
     \item $s: A vector of length NCOLLECT that saves MCMC draws for s, one of the parameters of the spike-slab prior.
     \item $tau: A data frame of size (NCOLLECT by N) that saves MCMC draws for the parameter tau of the horseshoe prior. 
     \item $lambda: A 3D array of size (N by number of latent factors by NCOLLECT) that saves MCMC draws for the parameter lambda of the horseshoe prior. 
  }
  
  }
}


\examples{
library(BCEndo)

data("df_eligible")   

OutcomeEqInfo <- list(Y = "Y",                                                  # the outcome variable 
                      D = "D",                                                  # the treatment indicator
                      Xp = c("X1", "X2"),                                       # mediators
                      Xq = c("X3", "X4", "X5", "X6", "X7", "X8", "X9"),         # exogenous covariates 
                      Xdelta = c("Xdelta1", "Xdelta2", "Xdelta3",               # covariates for delta_{y,it}, the direct effect
                                 "Xdelta4", "Xdelta5", "time"),                            
                      treat = "treat",                                          # identifier of treatment units
                      nFactor = 3,                                              # number of latent factors 
                      re = "unit",                                              # random effect specification (none, unit, time, or both)
                      estimate_individual_coefs = 1,                            # whether to estimate unit-specific coefficients (1 or 0)
                      estimate_time_varying_coefs = 1,                          # whether to estimate time-varying coefficients
                      estimate_phi_delta = 1,                                   # whether to estimate phi_delta (1 or 0)
                      factor_selection_method = "spike-slab"                    # factor selection method, either "horseshoe" or "spike-slab"
)

MediatorEqInfo <- list(P = as.list(OutcomeEqInfo$Xp),                           # mediators
                       X = list(c("XP1_1", "XP1_2", "XP1_3"),                   # covariates that explain the mediators
                                c("XP2_1", "XP2_2", "XP2_3")),
                       Xdelta = list(c("time"), c("time")),
                       nFactor = c(3, 3),                                       # number of latent factors for mediator equations
                       re = c("unit", "unit"),                                  # random effect specification (none, unit, time, or both)  
                       estimate_individual_coefs = c(1, 1),                     # whether to estimate unit-specific coefficients (1 or 0)
                       estimate_time_varying_coefs = c(1, 1),                   # whether to estimate time-varying coefficients
                       impute_p0_mis = c(1, 1),                                 # whether to impute the counterfactual potential covariates under no treatment
                       estimate_phi_delta = c(1, 1),                            # whether to estimate phi_delta (1 or 0)
                       factor_selection_method = c("spike-slab", "spike-slab")  # factor selection method, either "horseshoe" or "spike-slab"
                       
)

res <- BCEndo(data = df_eligible,
        index = c("id", "time"),
        OutcomeEqInfo = OutInfo,
        MediatorEqInfo = MediatorInfo,
        NBURN = 1000, 
        THIN = 1, 
        NCOLLECT = 1000)
        
plot_treatment_effects(res)
  
}
\seealso{
\code{plot_treatment_effects()}
}
\concept{test}
