\name{plot_treatment_effects}
\alias{plot_treatment_effects}
\title{Plot the treatment effects}
\description{
Use the output from \code{BCEndo()} and plot treatment effects.
}

\usage{
plot_treatment_effects(res)
}

\arguments{
\item{res}{output from \code{BCEndo()}. 
}
}

\value{
  \itemize{
  \item Plot of treatment's effects on mediators
  \item Plot of total treatment effect on the outcome
  \item Plot of mediated treatment effect on the outcome
  \item Plot of direct treatment effect on the outcome
}
}

\examples{

library(BCEndo)

data("df_eligible")   

OutInfo <- list(Y = "Y",                                                                            # the outcome variable 
                D = "D",                                                                            # the treatment indicator (1 or 0)
                Xp = c("X1", "X2"),                                                                 # mediators
                Xq = c("X3", "X4", "X5", "X6", "X7", "X8", "X9"),                                   # exogenous covariates
                Xdelta = c("Xdelta1", "Xdelta2", "Xdelta3", "Xdelta4", "Xdelta5"),                  # covariates for delta_{y,it} 
                treat = "treat",                                                                    # identifier of treatment units (1 or 0)
                nFactor = 3,                                                                        # number of common factors 
                re = "unit",                                                                        # random effect specification (none, unit, time, or both)
                estimate_individual_coefs = 1,                                                      # whether to estimate unit-specific coefficients (1 or 0)
                estimate_time_varying_coefs = 1,                                                    # whether to estimate time-varying coefficients
                estimate_phi_delta_y = 1,                                                           # whether to estimate phi_delta (1 or 0)
                addTimeTreandforDelta = 1,                                                          # whether to add a linear deterministic time trend in explaining residual effect, delta_{y,it}
                addInterceptforDelta = 1,                                                           # whether to add an intercept in explaining residual effect, delta_{y,it}
                variable_selection_method = "spike-slab"                                            # factor selection method, either "horseshoe" or "spike-slab"
)

MediatorInfo <- list(P = as.list(OutInfo$Xp),                                                       # mediators
                 X = list(c("XP1_1", "XP1_2", "XP1_3"),                                             # covariates that explain the mediators
                          c("XP2_1", "XP2_2", "XP2_3")),
                 nFactor = c(3, 3),                                                                 # number of common factors for mediator equations
                 re = c("unit", "unit"),                                                            # random effect specification (none, unit, time, or both)  
                 estimate_individual_coefs = c(1, 1),                                               # whether to estimate unit-specific coefficients (1 or 0)
                 estimate_time_varying_coefs = c(1, 1),                                             # whether to estimate time-varying coefficients
                 impute_p0_mis = c(1, 1),                                                           # whether to impute the counterfactual potential mediators under no treatment
                 variable_selection_method = c("spike-slab", "spike-slab")                          # factor selection method, either "horseshoe" or "spike-slab"
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
\code{BCEndo()}
}
