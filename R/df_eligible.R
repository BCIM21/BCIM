#' @title Sample Data with One Endogeneous Mediator
#' @description A sample data set to run the BCEndo function
#'
#' @docType data
#'
#' @usage data(df_eligible)
#'
#' @format A data frame with 2000 observations (50 units and 40 time periods each unit) and 31 variables. 
#' The first seven units are treatment units. Each of the seven units adopts the treatment in period 26. 
#' Thus, there are 25 pre-treatment periods and 15 treatment periods:
#' \describe{
#'  \item{id}{unit id, 1, 2, ..., 50}
#'  \item{time}{time index, 1, 2,..., 40}
#'  \item{Y}{the outcome variable}
#'  \item{D}{the treatment indicator 1 or 0. varies at the unit-time level}
#'  \item{total_eff}{the true total effect of treatment D on the outcome variable Y}
#'  \item{direct_eff}{the true direct effect of treatment D on the outcome variable Y, the treatment effect not transmitted through mediators}
#'  \item{mediated_eff}{the true effect of treatment D on the outcome variable Y through the mediators, X1 and X2}
#'  \item{X1}{the endogenous mediator. It shares a latent factor with the outcome variable. The shared latent factor is a confounder that makes the mediator endogenous}
#'  \item{X2}{the exogenous mediator. It does not share  a latent factor with the outcome variable.}
#'  \item{X3 - X9}{Seven exogenous covarates. They do not change with treatment adopiton D}
#'  \item{treat}{indicator for treatment unit. varies at the unit level}
#'  \item{time_diff}{relative time difference -24, -23, ..., 0, 1, 2, ..., 15}
#'  \item{Xdelta1 - Xdelta5}{variables that explain the pure treatment effect "pure_eff"}
#'  \item{XP1_1 - XP1_3}{exogenous variables that explain the first endogenous covariate X1}
#'  \item{XP2_1 - XP2_3}{exogenous variables that explain the second endogenous covariatge X2}
#'  \item{p_eff1}{the true effect of treatment D on mediator X1}
#'  \item{p_eff2}{the true effect of treatment D on mediator X2}
#'      
#' }
#' @keywords datasets
#'
#' @examples
#' data(df_eligible)
#' 
#' res <- BCEndo(data = df_eligible,   
#'                index = c("id", "time"),
#'                OutcomeEqInfo = OutcomeEqInfo,
#'                CovariateEqInfo = CovariateEqInfo,
#'                NBURN = 1000,
#'                THIN = 1,
#'                NCOLLECT = 1000) 
"df_eligible"