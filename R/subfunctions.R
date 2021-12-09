#--------------------- fundamental functions -------------------#

# draw from regression coefficients

draw_regcoef <- function(y, X, sigma2, B0) {
  B <- solve(  1/sigma2*crossprod(X) + solve(B0)  )
  beta <- B%*%(1/sigma2*crossprod(X,y))
  
  return(rmvnorm(n = 1, mean = beta, sigma = B))
}

draw_regcoef_overparam <- function(y, X, sigma2, b0, B0) {
  B <- solve(  1/sigma2*crossprod(X) + solve(B0)  )
  beta <- B%*%(1/sigma2*crossprod(X,y) + solve(B0)%*%b0)
  
  return(rmvnorm(n = 1, mean = beta, sigma = B))
}

ffbs <- function(m0, C0, Y, F, G, V, W, N, TT) {
  
  # Y(t) = F(t)%*%theta(t) + nu(t)
  # theta(t) = G%*%theta(t-1) + omega(t)
  # V = var(nu(t))
  # W = var(omega(t))
  
  k <- length(m0)
  theta <- m <- a <-  h <- matrix(0, nrow =length(m0), ncol = TT)
  
  if(k == 1) {
    R <- C <- B <- H <- replicate(TT, diag(k))  |> array(dim = c(1,1,TT  ))
  } else {
    R <- C <- B <- H <- replicate(TT, diag(k))  
  }
  
  
  e <- f <- Y
  Q <- replicate(TT, diag(N))
  A <- replicate(TT, matrix(0, nrow = k, ncol = N))
  
  # FF
  for (t in 1:TT) {
    if (t == 1) {
      a[,t] <- G%*%m0; R[,,t] <- G%*%C0%*%t(G) + W    
    } else {
      a[,t] <- G%*%m[,t-1]; R[,,t] <- G%*%C[,,t-1]%*%t(G) + W  
    }
    
    f[,t] <- F[,,t]%*%as.matrix(a[,t]); Q[,,t] <- F[,,t]%*%as.matrix(R[,,t])%*%t(F[,,t]) + V
    
    A[,,t] <- R[,,t]%*%t(F[,,t])%*%solve(Q[,,t]); e[,t] <- Y[,t] - f[,t]
    m[,t] <- a[,t] + A[,,t]%*%e[,t]; C[,,t] <- R[,,t] - A[,,t]%*%Q[,,t]%*%t( matrix(A[,,t], nrow = dim(A)[1]) )  ## orginally t(A[,,t]); revised for intercept only case
  }
  
  # BS
  
  for(t in TT:1) {
    if (t == TT) {
      theta[,t] <- rmvnorm(1, m[,t], (C[,,t] + t(C[,,t]))/2  )
    } else {
      B[,,t] <- C[,,t]%*%t(G)%*%solve(R[,,t+1])
      H[,,t] <- C[,,t] - B[,,t]%*%R[,,t+1]%*%t(B[,,t])
      h[,t] <- m[,t] + B[,,t]%*%(theta[,t+1] - a[,t+1])
      theta[,t] <- rmvnorm(1, h[,t], (H[,,t] + t(H[,,t]))/2 )
    }
  }
  
  return(list(theta = theta))
  
}

horseshoe <- function (y, X, Sigma2 = 1, tau, lambda) {
  n <- nrow(X)
  p <- ncol(X)
  Beta <- rep(0, p)
  sigma_sq  <- Sigma2
  
  I_n <- diag(n)
  l0 <- rep(0, p)
  l1 <- rep(1, n)
  l2 <- rep(1, p)
  
  if (p > n) {
    lambda_star <- tau * lambda
    U <- as.numeric(lambda_star^2) * t(X)
    u <- stats::rnorm(l2, l0, lambda_star)
    v <- X %*% u + stats::rnorm(n)
    v_star <- solve((X %*% U + I_n), ((y/sqrt(sigma_sq)) - v))
    Beta = sqrt(sigma_sq) * (u + U %*% v_star)
  } else {
    Q_star <- crossprod(X)
    lambda_star <- tau * lambda
    L <- chol(    (1/sigma_sq) * (    Q_star + diag(1/as.numeric(lambda_star^2), p, p)    )     )
    v <- solve(t(L), t(t(y) %*% X)/sigma_sq)
    mu <- solve(L, v)
    u <- solve(L, stats::rnorm(p))
    Beta <- mu + u
  }
  
  eta <- 1/(lambda^2)
  upsi <- stats::runif(p, 0, 1/(1 + eta))
  tempps <- Beta^2/(2 * sigma_sq * tau^2)
  ub <- (1 - upsi)/upsi
  Fub <- 1 - exp(-tempps * ub)
  Fub[Fub < (1e-04)] = 1e-04
  up <- stats::runif(p, 0, Fub)
  eta <- -log(1 - up)/tempps
  lambda <- 1/sqrt(eta)
  
  tempt <- sum((Beta/lambda)^2)/(2 * sigma_sq)
  et <- 1/tau^2
  utau <- stats::runif(1, 0, 1/(1 + et))
  ubt_1 <- 1
  ubt_2 <- min((1 - utau)/utau, p^2)
  Fubt_1 <- stats::pgamma(ubt_1, (p + 1)/2, scale = 1/tempt)
  Fubt_2 <- stats::pgamma(ubt_2, (p + 1)/2, scale = 1/tempt)
  ut <- stats::runif(1, Fubt_1, Fubt_2)
  et <- stats::qgamma(ut, (p + 1)/2, scale = 1/tempt)
  tau <- 1/sqrt(et)
  
  res <- list(Beta = Beta, tau = tau, lambda = lambda)
  
  return(res)
}

#--------------------- MCMC steps -------------------#

###### Step 1-1
## (a) draw beta_p
draw_beta_p0_l <- function(datP, paramp) {
  TT <- datP$TT
  N <- datP$N
  N_co <- datP$N_co
  N_tr <- datP$N_tr
  T0 <- datP$T0
  k_y1 <- datP$k_y1
  treated_ids <- datP$treated_unit_ids
  ctrl_ids <- datP$control_unit_ids
  treated_idx_by_unit <- datP$treated_idx_by_unit
  ctrl_idx_by_unit <- datP$ctrl_idx_by_unit
  treated_idx <- datP$treated_idx
  ctrl_idx <- datP$ctrl_idx
  
  X <- as.matrix(datP$Xp[ctrl_idx, ])
  
  alpha <- paramp$alpha_i
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- as.matrix(alpha[rows,])
  alpha <- alpha[ctrl_idx,]
  
  xi <- paramp$xi_t
  rows <- rep(1:nrow(xi), N)
  xi <- xi[rows,]
  xi <- xi[ctrl_idx, ]
  
  gamma <- paramp$gamma_i
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- as.matrix(gamma[rows,])
  gamma <- gamma[ctrl_idx,]
  
  f_p_t <- paramp$f_p_t
  rows <- rep(1:nrow(f_p_t), N)
  f_p_t <- as.matrix(f_p_t[rows,])
  f_p_t <- f_p_t[ctrl_idx, ]
  
  u <- datP$dat$p[ctrl_idx] - rowSums(X*alpha + X*xi) - rowSums(as.matrix(f_p_t*gamma))
  
  sigma2 <- paramp$sigma2
  
  k <- ncol(X)
  B0 <- diag(k)*1000
  
  beta <- draw_regcoef(u, X, sigma2, B0) |> t()
  
  return(beta)
}

## (b-0) draw individual intercept
draw_individual_intercept_p0_i_l_overparam <- function(datP, paramp) {
  TT <- datP$TT
  N <- datP$N
  N_co <- datP$N_co
  N_tr <- datP$N_tr
  T0 <- datP$T0
  k_y1 <- datP$k_y1
  treated_ids <- datP$treated_unit_ids
  ctrl_ids <- datP$control_unit_ids
  treated_idx_by_unit <- datP$treated_idx_by_unit
  ctrl_idx_by_unit <- datP$ctrl_idx_by_unit
  treated_idx <- datP$treated_idx
  ctrl_idx <- datP$ctrl_idx
  
  
  dat <- datP$dat
  beta <- paramp$beta  
  X <- as.matrix(datP$Xp)
  k <- ncol(X)
  X_intercept <- X[, k] |> as.matrix()
  k_intercept <- 1
  
  X_ <- X[, 1:(k-1)] |> as.matrix()
  k_ <- ncol(X_)
  
  intercept_i <- vector(mode = "numeric", length = N)
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT)  
    dat_i <- dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    X_i <- X[idx, ]
    X_i <- X_i[ctrl_idx_by_unit[[i]], ]
    
    X_i_intercept <- X_intercept[idx, ] |> as.matrix()
    X_i_intercept <- X_i_intercept[ctrl_idx_by_unit[[i]], ] |> as.matrix()
    
    X_i_ <- X_[idx, ] |> as.matrix()
    X_i_ <- X_i_[ctrl_idx_by_unit[[i]], ] |> as.matrix()
    
    alpha_i_ <- paramp$alpha_i[, 1:k_]
    alpha_i_ <- alpha_i_[i,]
    alpha_ <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i_), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    
    xi_t <- paramp$xi_t[ctrl_idx_by_unit[[i]],]
    gamma <- paramp$gamma_i[i,]
    gamma <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), gamma), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    f_p_t <- matrix(paramp$f_p_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    u_i <- dat_i$p - X_i%*%beta- rowSums(X_i_*alpha_)  - rowSums(X_i*xi_t) - rowSums(f_p_t*gamma)
    
    sigma2 <- paramp$sigma2
    b0 = as.numeric(paramp$mu_alpha[k])
    B0 = paramp$Sigma_alpha[k,k]
    intercept_i[i] <- draw_regcoef_overparam(u_i, X_i_intercept, sigma2, b0, B0)
  }
  
  mu_intercept <- draw_regcoef(y = intercept_i, X = rep(1, N), sigma2 = paramp$Sigma_alpha[k,k], B0 = 1000)  
  
  u <- intercept_i - c(mu_intercept)
  
  a1 <- N/2 + 0.001
  a2 <- sum(u^2)/2 + 0.001
  Sigma_intercept <- 1/rgamma(1, a1, a2) 
  
  res_list = list(intercept_i = intercept_i,
                  mu_intercept = mu_intercept,
                  Sigma_intercept = Sigma_intercept)  
  
  return(res_list)
}

## (b) draw alpha_p_i 
draw_alpha_p0_i_l_overparam <- function(datP, paramp) {
  N <- datP$N
  N_co <- datP$N_co
  N_tr <- datP$N_tr
  T0 <- datP$T0
  k_y1 <- datP$k_y1
  treated_ids <- datP$treated_unit_ids
  ctrl_ids <- datP$control_unit_ids
  treated_idx_by_unit <- datP$treated_idx_by_unit
  ctrl_idx_by_unit <- datP$ctrl_idx_by_unit
  treated_idx <- datP$treated_idx
  ctrl_idx <- datP$ctrl_idx
  
  dat <- datP$dat
  beta <- paramp$beta  
  X <- as.matrix(datP$Xp)
  k <- ncol(X)
  
  alpha_i <- matrix(0, nrow = N, ncol = k-1)
  mu_alpha <- vector(mode = "numeric", length = k-1)
  Sigma_alpha <- matrix(0, nrow = k-1, ncol = k-1)
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT)  
    dat_i <- dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    X_i <- X[idx, ]
    X_i <- X_i[ctrl_idx_by_unit[[i]], ]
    
    X_i_for_alpha <- X_i[,-k]
    
    alpha_i_for_intercept <- paramp$alpha_i[i,k]
    alpha_i_for_intercept <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i_for_intercept), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    
    xi_t <- paramp$xi_t[ctrl_idx_by_unit[[i]],]
    gamma <- paramp$gamma_i[i,]
    gamma <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), gamma), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    f_p_t <- matrix(paramp$f_p_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    
    u_i <- dat_i$p - X_i%*%beta - alpha_i_for_intercept  - rowSums(X_i*xi_t) - rowSums(f_p_t*gamma)
    
    sigma2 <- paramp$sigma2
    b0 = as.numeric(paramp$mu_alpha[-k])
    B0 = paramp$Sigma_alpha[-k,-k]
    alpha_i[i,] <- draw_regcoef_overparam(u_i, X_i_for_alpha, sigma2, b0, B0)
  }
  
  nvar <- ncol(paramp$alpha_i) - 1  ## because intercept is not estimated here
  
  for (j in 1:nvar) {
    mu_alpha[j] <- draw_regcoef(y = alpha_i[,j], X = rep(1, N), sigma2 = paramp$Sigma_alpha[j,j], B0 = 1000)  
    
    u <- alpha_i[,j] - mu_alpha[j]
    
    a1 <- N/2 + 0.001
    a2 <- sum(u^2)/2 + 0.001
    Sigma_alpha[j,j] <- 1/rgamma(1, a1, a2) 
  }
  
  res_list = list(alpha_i = alpha_i,
                  mu_alpha = mu_alpha,
                  Sigma_alpha = Sigma_alpha)
  
  return(res_list)
}

## (c) gamma_p_i
draw_gamma_p0_i_l <- function(datP, paramp) {
  N <- datP$N
  N_co <- datP$N_co
  N_tr <- datP$N_tr
  T0 <- datP$T0
  k_y1 <- datP$k_y1
  treated_ids <- datP$treated_unit_ids
  ctrl_ids <- datP$control_unit_ids
  treated_idx_by_unit <- datP$treated_idx_by_unit
  ctrl_idx_by_unit <- datP$ctrl_idx_by_unit
  treated_idx <- datP$treated_idx
  ctrl_idx <- datP$ctrl_idx
  
  X_for_gamma <- paramp$f_p_t
  k <- ncol(X_for_gamma)
  X <- as.matrix(datP$Xp)
  B0 <- paramp$sigma2*paramp$tau2*diag(k)
  
  beta <- paramp$beta
  
  r_pl <- ncol(paramp$gamma_i)
  
  gamma_i <- matrix(nrow = N, ncol = r_pl)
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT) 
    dat_i <- datP$dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    X_i <- X[idx, ]
    X_i <- X_i[ctrl_idx_by_unit[[i]], ]
    alpha_i <- paramp$alpha_i[i, ]
    alpha_i <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    xi_t <- matrix(paramp$xi_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    
    u_i <- dat_i$p - X_i%*%beta - rowSums(X_i*(alpha_i + xi_t))
    
    X_for_gamma_i <- X_for_gamma[ctrl_idx_by_unit[[i]],]
    sigma2 <- paramp$sigma2
    
    gamma_i[i,] <- draw_regcoef(u_i, X_for_gamma_i, sigma2, B0)
    
  }
  
  return(gamma_i)
}
draw_gamma_p0_i_l_hs <- function(datP, paramp) {
  N <- datP$N
  N_co <- datP$N_co
  N_tr <- datP$N_tr
  T0 <- datP$T0
  k_y1 <- datP$k_y1
  treated_ids <- datP$treated_unit_ids
  ctrl_ids <- datP$control_unit_ids
  treated_idx_by_unit <- datP$treated_idx_by_unit
  ctrl_idx_by_unit <- datP$ctrl_idx_by_unit
  treated_idx <- datP$treated_idx
  ctrl_idx <- datP$ctrl_idx
  TT <- datP$TT
  
  X_for_gamma <- paramp$f_p_t
  k <- ncol(X_for_gamma)
  X <- as.matrix(datP$Xp)
  B0 <- paramp$sigma2*paramp$tau2*diag(k)
  
  beta <- paramp$beta
  
  gamma_i_res <- paramp$gamma_i
  tau_res <- paramp$tau
  lambda_res <- paramp$lambda
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT) 
    dat_i <- datP$dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    X_i <- as.matrix(X[idx, ])
    X_i <- as.matrix(X_i[ctrl_idx_by_unit[[i]], ])
    alpha_i <- paramp$alpha_i[i, ]
    alpha_i <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    xi_t <- matrix(paramp$xi_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    
    u_i <- dat_i$p - X_i%*%beta - rowSums(X_i*(alpha_i + xi_t))
    
    X_for_gamma_i <- X_for_gamma[ctrl_idx_by_unit[[i]],]
    sigma2 <- paramp$sigma2
    tau <- paramp$tau[i]
    lambda <- paramp$lambda[i,]
    
    res <- horseshoe(y = u_i, X = X_for_gamma_i, Sigma2 = sigma2, tau = tau, lambda = lambda)
    
    gamma_i_res[i,] <- res$Beta
    tau_res[i] <- res$tau
    lambda_res[i,] <- res$lambda
  }
  
  res_list <- list(gamma_i = gamma_i_res, tau = tau_res, lambda = lambda_res)
  
  return(res_list)
}

## (d) 
draw_xi_f_p0_t_l <- function(dataP, paramp0, estimate_timevarying_coefs) {
  
  k_y1 <- dataP$k_y1
  ctrl_ids <- dataP$control_unit_ids
  treated_ids <- dataP$treated_unit_ids
  ctrl_idx <- which(dataP[[1]]$dat$treat == 0)
  N_co <- length(ctrl_ids)
  N_tr <- length(treated_ids)
  TT <- dataP$TT
  
  for (l in 1:k_y1) {
    dat <- dataP[[l]] 

    k1 <- length(paramp0[[l]]$beta) 
    r_pl <- ncol(as.matrix(paramp0[[l]]$f_p_t))
    k <- k1 + r_pl
    m0 <- rep(0, k)
    C0 <- diag(k)
    
    X <- as.matrix(dat$Xp[ctrl_idx,])
    
    beta <- paramp0[[l]]$beta
    
    alpha <- paramp0[[l]]$alpha_i[ctrl_ids,] 
    rows <- rep(1:nrow(alpha), each = TT)
    alpha <- alpha[rows,]
    
    gamma <- as.matrix(paramp0[[l]]$gamma_i[ctrl_ids,])
    rows <- rep(1:nrow(gamma), each = TT)
    gamma <- gamma[rows,]
    
    
    u <- (dat$dat$p[ctrl_idx] - X%*%beta - rowSums(X*alpha))  |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
    if (estimate_timevarying_coefs == 1) {
      Z <- cbind(X, gamma)  # F
      W <- diag(c(diag(paramp0[[l]]$sigma2e), rep(1,  r_pl  )))
      Phi <- diag(   c(diag(paramp0[[l]]$phi_xi), diag(paramp0[[l]]$phi_f)   )  )  # G
    } else {
      Z <- gamma
      W <- diag(rep(1,  r_pl))
      Phi <- diag(paramp0[[l]]$phi_f)
    }
    
    if (length(paramp0[[l]]$phi_f == 1)) paramp0[[l]]$phi_f <- as.matrix(paramp0[[l]]$phi_f)
    
    V <- paramp0[[l]]$sigma2*diag(N_co)   #V
    
    rows <- NULL
    for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
    Z2 <- Z[rows, ]
    
    rows <- NULL
    Z3 <- array(numeric(),c(N_co,k,TT)) 
    for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
    res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
    
    paramp0[[l]]$xi_t <- t(res$theta)[, 1:k1]
    paramp0[[l]]$f_p_t <- t(res$theta)[, (k1+1):(k1+r_pl)]
  }
  return(paramp0)
}

draw_xi_p0_t_l <- function(datP, paramp) {
  k_y1 <- datP$k_y1
  ctrl_ids <- datP$control_unit_ids
  treated_ids <- datP$treated_unit_ids
  ctrl_idx <- which(datP$dat$treat == 0)
  N_co <- length(ctrl_ids)
  N_tr <- length(treated_ids)
  TT <- datP$TT
  
  k1 <- length(paramp$beta) 
  r_pl <- ncol(as.matrix(paramp$f_p_t))
  k <- k1 + r_pl
  m0 <- rep(0, k1 - 1)  # k1 -1 because intercept is removed
  C0 <- diag(k1 - 1)  # k1 -1 because intercept is removed
  
  X <- as.matrix(datP$Xp[ctrl_idx,])
  
  beta <- paramp$beta
  
  alpha <- paramp$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  gamma <- as.matrix(paramp$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  f_p_t <- as.matrix(paramp$f_p_t)
  rows <- rep(1:nrow(f_p_t), N_co)
  f_p_t <- f_p_t[rows,]
  
  u <- (datP$dat$p[ctrl_idx] - X%*%beta - rowSums(X*alpha) - rowSums(gamma*f_p_t) ) |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  ncol_X <- ncol(X)
  
  W <- paramp$sigma2e[-ncol_X, -ncol_X]
  Phi <- paramp$phi_xi[-ncol_X, -ncol_X]  # G
  V <- paramp$sigma2*diag(N_co)   #V
  
  
  Z <- X[,-ncol_X]  # F  # to remove the intercept
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ]
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,k1 - 1,TT))   # k1 - 1 because intercept is removed
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  xi_t <- t(res$theta)
  
  return(xi_t)
}
draw_xi_p0_t_l_with_intercept <- function(datP, paramp) {
  k_y1 <- datP$k_y1
  ctrl_ids <- datP$control_unit_ids
  treated_ids <- datP$treated_unit_ids
  ctrl_idx <- which(datP$dat$treat == 0)
  N_co <- length(ctrl_ids)
  N_tr <- length(treated_ids)
  TT <- datP$TT
  
  k1 <- length(paramp$beta) 
  r_pl <- ncol(as.matrix(paramp$f_p_t))
  k <- k1 + r_pl
  m0 <- rep(0, k1)
  C0 <- diag(k1)
  
  X <- as.matrix(datP$Xp[ctrl_idx,])
  
  beta <- paramp$beta
  
  alpha <- paramp$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  gamma <- as.matrix(paramp$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  f_p_t <- as.matrix(paramp$f_p_t)
  rows <- rep(1:nrow(f_p_t), N_co)
  f_p_t <- f_p_t[rows,]
  
  u <- (datP$dat$p[ctrl_idx] - X%*%beta - rowSums(X*alpha) - rowSums(gamma*f_p_t) ) |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  W <- paramp$sigma2e
  Phi <- paramp$phi_xi  # G
  V <- paramp$sigma2*diag(N_co)   #V
  
  Z <- X  # F
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ]
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,k1,TT)) 
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  xi_t <- t(res$theta)
  
  return(xi_t)
}
draw_xi_p0_t_l_intercept_only <- function(datP, paramp) {
  k_y1 <- datP$k_y1
  ctrl_ids <- datP$control_unit_ids
  treated_ids <- datP$treated_unit_ids
  ctrl_idx <- which(datP$dat$treat == 0)
  N_co <- length(ctrl_ids)
  N_tr <- length(treated_ids)
  TT <- datP$TT
  
  k1 <- length(paramp$beta) 
  r_pl <- ncol(as.matrix(paramp$f_p_t))
  k <- k1 + r_pl
  m0 <- 0 |> as.matrix()
  C0 <- 1 |> as.matrix()
  
  X <- as.matrix(datP$Xp[ctrl_idx,])
  
  beta <- paramp$beta
  
  alpha <- paramp$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  gamma <- as.matrix(paramp$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  f_p_t <- as.matrix(paramp$f_p_t)
  rows <- rep(1:nrow(f_p_t), N_co)
  f_p_t <- f_p_t[rows,]
  
  u <- (datP$dat$p[ctrl_idx] - X%*%beta - rowSums(X*alpha) - rowSums(gamma*f_p_t) ) |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  ncol_X <- ncol(X)
  W <- paramp$sigma2e[ncol_X, ncol_X]  |> as.matrix()
  Phi <- paramp$phi_xi[ncol_X, ncol_X] |> as.matrix()    # G
  V <- paramp$sigma2*diag(N_co)   #V
  
  Z <- X[,ncol_X] |> matrix(nrow = nrow(X)) # F  # include intercept only
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ] |> as.matrix()
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,1,TT))   # 1 because only intercept is included
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  xi_t <- t(res$theta)
  
  return(xi_t)
}

draw_f_p0_t_l <- function(datP, paramp) {
  
  k_y1 <- datP$k_y1
  ctrl_ids <- datP$control_unit_ids
  treated_ids <- datP$treated_unit_ids
  ctrl_idx <- which(datP$dat$treat == 0)
  N_co <- length(ctrl_ids)
  N_tr <- length(treated_ids)
  TT <- datP$TT
  
  k1 <- length(paramp$beta) 
  r_pl <- ncol(as.matrix(paramp$f_p_t))
  k <- k1 + r_pl
  m0 <- rep(0, r_pl)
  C0 <- diag(r_pl)
  
  X <- as.matrix(datP$Xp[ctrl_idx,])
  
  beta <- paramp$beta
  
  alpha <- paramp$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  gamma <- as.matrix(paramp$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  xi <- as.matrix(paramp$xi)
  rows <- rep(1:nrow(xi), N_co)
  xi <- xi[rows, ]
  
  u <- (datP$dat$p[ctrl_idx] - X%*%beta - rowSums(X*alpha)  - rowSums(X*xi)) |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  W <- diag(rep(1,  r_pl))
  Phi <- paramp$phi_f
  
  if (length(paramp$phi_f == 1)) paramp$phi_f <- as.matrix(paramp$phi_f)
  V <- paramp$sigma2*diag(N_co)   #V
  
  Z <- gamma
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ]
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,r_pl,TT)) 
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  f_p_t <- t(res$theta)
  
  return(f_p_t)
}

## (e) draw phi_p_xi_l
draw_phi_xi_p0_j_l <- function(dataP, paramp0) {
  k_y1 <- dataP$k_y1
  ctrl_ids <- dataP$control_unit_ids
  treated_ids <- dataP$treated_unit_ids
  ctrl_idx <- which(dataP[[1]]$dat$treat == 0)
  N_co <- length(ctrl_ids)
  N_tr <- length(treated_ids)
  TT <- dataP$TT
  
  for (l in 1:k_y1) {
    param <- paramp0[[l]]
    J <- ncol(param$xi_t)
    
    for(j in 1:J) {
      y <- param$xi_t[,j]
      X <- c(0, y[1:(length(y) - 1)])
      B0 <- 1000
      sigma2e <- param$sigma2e[j,j]
      
      paramp0[[l]]$phi_xi[j, j] <- draw_regcoef(y, X, sigma2e, B0)
    }
  }
  return(paramp0)
}
draw_phi_xi_sigma2_e_p0_j_l <- function(dataP, paramp0) {
  k_y1 <- dataP$k_y1
  ctrl_ids <- dataP$control_unit_ids
  treated_ids <- dataP$treated_unit_ids
  ctrl_idx <- which(dataP[[1]]$dat$treat == 0)
  N_co <- length(ctrl_ids)
  N_tr <- length(treated_ids)
  TT <- dataP$TT
  
  for (l in 1:k_y1) {
    param <- paramp0[[l]]
    J <- ncol(param$xi_t)
    
    for(j in 1:J) {
      y <- param$xi_t[,j]
      X <- c(0, y[1:(length(y) - 1)])
      B0 <- 1000
      sigma2e <- param$sigma2e[j,j]
      
      paramp0[[l]]$phi_xi[j, j] <- draw_regcoef(y, X, sigma2e, B0)
      
      u <- y - paramp0[[l]]$phi_xi[j,j]*X
      paramp0[[l]]$sigma2e[j,j] <- 1/rgamma(1, TT/2 + 0.001, sum(u^2)/2 + 0.001)
      
    }
  }
  return(paramp0)
}

## (f) draw_phi_p_f_l
draw_phi_f_p0_j_l <- function(datP, paramp) {
  
  J <- ncol(paramp$f_p_t)
  
  phi_f <- paramp$phi_f
  
  for(j in 1:J) {
    y <- paramp$f_p_t[,j]
    X <- c(0, y[1:(length(y) - 1)])
    B0 <- 1000
    sigma2f <- 1
    
    phi_f[j, j] <- draw_regcoef(y, X, sigma2f, B0)
  }
  
  return(phi_f)
}

## (g) draw_sigma2_p_e_l 
draw_sigma2_e_p0_j_l <- function(datP, paramp) {
  
  TT <- datP$TT
  J <- ncol(paramp$xi_t)
  
  sigma2e <- paramp$sigma2e
  
  for(j in 1:J) {
    y <- paramp$xi_t[,j]
    X <- c(0, y[1:(length(y) - 1)])
    u <- y - paramp$phi_xi[j,j]*X
    
    sigma2e[j,j] <- 1/rgamma(1, TT/2 + 0.001, sum(u^2)/2 + 0.001)
  }
  
  return(sigma2e)
}

## (h) 
draw_sigma2_eps_p0_l <- function(datP, paramp) {
  N <- datP$N
  N_co <- datP$N_co
  N_tr <- datP$N_tr
  T0 <- datP$T0
  k_y1 <- datP$k_y1
  treated_ids <- datP$treated_unit_ids
  ctrl_ids <- datP$control_unit_ids
  treated_idx_by_unit <- datP$treated_idx_by_unit
  ctrl_idx_by_unit <- datP$ctrl_idx_by_unit
  treated_idx <- datP$treated_idx
  ctrl_idx <- datP$ctrl_idx
  N_obs <- length(ctrl_idx)
  
  X <- as.matrix(datP$Xp[ctrl_idx, ])
  beta <- paramp$beta
  
  alpha <- paramp$alpha_i
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  alpha <- alpha[ctrl_idx,]
  
  xi <- paramp$xi_t
  rows <- rep(1:nrow(xi), N)
  xi <- xi[rows,]
  xi <- xi[ctrl_idx, ]
  
  gamma <- paramp$gamma_i
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- as.matrix(gamma[rows,])
  gamma <- gamma[ctrl_idx,]
  
  f_p_t <- paramp$f_p_t
  rows <- rep(1:nrow(f_p_t), N)
  f_p_t <- as.matrix(f_p_t[rows,])
  f_p_t <- as.matrix(f_p_t[ctrl_idx, ])
  
  u <- datP$dat$p[ctrl_idx] - X%*%beta - rowSums(X*alpha + X*xi) - rowSums(f_p_t*gamma)
  
  sigma2 <- 1/rgamma(1, N_obs/2 + 0.001, sum(u^2)/2 + 0.001)
  
  return(sigma2)
}

## (i)
draw_pi_p0_j_l <- function(datP, paramp) {
  TT <- datP$TT
  N <- datP$N
  N_co <- datP$N_co
  N_tr <- datP$N_tr
  T0 <- datP$T0
  k_y1 <- datP$k_y1
  treated_ids <- datP$treated_unit_ids
  ctrl_ids <- datP$control_unit_ids
  treated_idx_by_unit <- datP$treated_idx_by_unit
  ctrl_idx_by_unit <- datP$ctrl_idx_by_unit
  treated_idx <- datP$treated_idx
  ctrl_idx <- datP$ctrl_idx
  N_obs <- length(ctrl_idx)
  
  J <- ncol(paramp$f_p_t)
  
  theta_p0_l <- paramp$theta
  sigma2_eps <- paramp$sigma2
  tau2 <- paramp$tau2
  
  beta <- paramp$beta
  
  gamma_i_res <- paramp$gamma_i
  pi <- vector(mode = "numeric", length = J)
  
  for (j in 1:J) {
    
    A1 <- theta_p0_l*(sigma2_eps*tau2)^(-N/2)
    
    tmp1 <- tmp2 <- rep(0, N)
    
    for (i in 1:N) {
      idx <- seq((i-1)*TT + 1, i*TT) 
      dat_i <- datP$dat[idx, ]
      dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
      X_i <- as.matrix(datP$Xp[idx, ])
      X_i <- X_i[ctrl_idx_by_unit[[i]], ]
      
      alpha_i <- paramp$alpha_i[i, ]
      alpha_i <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
      
      xi_t <- matrix(paramp$xi_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
      
      gamma_i <- paramp$gamma_i[i,]
      gamma_i <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), gamma_i), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
      
      f_p_t <- matrix(paramp$f_p_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
      
      cond_var_i <- (  sum(f_p_t[,j]^2) +  1/tau2 )
      
      z <- dat_i$p - X_i%*%beta - rowSums(X_i*alpha_i + X_i*xi_t) - rowSums(as.matrix(f_p_t[,-j]*gamma_i[,-j]))
      
      tmp1[i] <- sum(f_p_t[,j]*z)^2  / cond_var_i    
      tmp2[i] <- sqrt(sigma2_eps/cond_var_i)
      
    }
    
    one_minus_mu <- (1 - theta_p0_l) / (  A1*exp(  1/(2*sigma2_eps) * sum(tmp1)  )*prod(tmp2) + (1 - theta_p0_l)  )
    mu <- 1 - one_minus_mu
    
    pi[j] <- rbinom(1, size = 1, prob = mu)
  }
  
  # set gamma = 0 for pi = 0
  gamma_i_res[,which(pi == 0)] <- 0
  
  res_list = list(pi = pi, gamma_i = gamma_i_res)
  return(res_list)
}

## (j)
draw_theta_p0_l <- function(datP, paramp) {
  b1 <- 1 + sum(paramp$pi)
  b2 <- 1 + sum(1 - paramp$pi)
  
  theta <- rbeta(1, b1, b2)
  
  return(theta)
}

## (k)
draw_tau2_p0_l <- function(datP, paramp) {
  N_co <- datP$N_co
  N <- datP$N
  
  pi <- paramp$pi
  sigma2_eps <- paramp$sigma2
  gamma <- paramp$gamma_i
  s <- paramp$s
  
  a1 <- 1/2 + sum(pi)*N/2
  a2 <- s/2 + sum(gamma^2)/(2*sigma2_eps)
  
  tau2 <- 1/rgamma(1, a1, a2)
  
  return(tau2)
}

## (l)
draw_s_p0_l <- function(datP, paramp) {
  tau2 <- paramp$tau2
  s <- 1/rgamma(1, 0.01 + 1/2, 0.01 + 1/tau2)
  
  return(s)
}

###### Step 1-2
draw_p0_mis <- function(datP, paramp) {
  TT <- datP$TT
  N <- datP$N
  N_co <- datP$N_co
  N_tr <- datP$N_tr
  T0 <- datP$T0
  k_y1 <- datP$k_y1
  treated_ids <- datP$treated_unit_ids
  ctrl_ids <- datP$control_unit_ids
  treated_idx_by_unit <- datP$treated_idx_by_unit
  ctrl_idx_by_unit <- datP$ctrl_idx_by_unit
  treated_idx <- datP$treated_idx
  ctrl_idx <- datP$ctrl_idx
  
  X <- as.matrix(datP$Xp)
  beta <- paramp$beta
  
  mu_alpha <- as.vector(paramp$mu_alpha)
  
  alpha <- paramp$alpha_i
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  xi <- paramp$xi_t
  rows <- rep(1:nrow(xi), N)
  xi <- xi[rows,]
  
  gamma <- paramp$gamma_i
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  f_p_t <- paramp$f_p_t
  rows <- rep(1:nrow(f_p_t), N)
  f_p_t <- f_p_t[rows,]
  
  sigma2 <- paramp$sigma2
  
  mu <- X%*%(beta + mu_alpha) +  rowSums(X*(alpha - t( replicate(N*TT, mu_alpha) ) ) + X*xi) + rowSums(f_p_t*gamma)
  
  p0_mis <- rnorm(n = N*TT, mean = mu, sd = sqrt(sigma2))
  
  return(p0_mis)
}
draw_p0_delta <- function(datP, paramp){
  delta <-  datP$dat$p - paramp$p0_mis
  return(delta)
}

# draw phi delta p
draw_phi_delta_p <- function(dataP, paramp0, addTimeTrend = TRUE) {
  TT <- dataP$TT
  T0 <- dataP$T0
  N_tr <- dataP$N_tr
  treated_idx <- dataP$treated_idx
  
  # sigma2_eta <- paramp0$sigma2_eta
  sigma2_eta <- 2*paramp0$sigma2
  X <- dataP$Xdelta[treated_idx, ]
  
  timeindex <- vector(mode = "numeric")
  for(i in 1:N_tr) timeindex <- c(timeindex, 1:(TT-T0[i])   )
  if(addTimeTrend == 1) X <- cbind(timeindex, X)
  
  u <- paramp0$delta[treated_idx]
  Phi0 <- 1000*diag(ncol(X))
  
  paramp0$phi_delta <- draw_regcoef(u, X, sigma2_eta, Phi0) |> t()
  
  return(paramp0)
}

# draw sigma2_eta_p
draw_sigma2_eta_p <- function(dataP, paramp0, addTimeTrend = TRUE) {
  TT <- dataP$TT
  T0 <- dataP$T0
  N_tr <- dataP$N_tr
  treated_idx <- dataP$treated_idx
  
  N_obs <- length(treated_idx)
  X <- dataP$Xdelta[treated_idx, ] |> as.matrix()
  
  timeindex <- vector(mode = "numeric")
  for(i in 1:N_tr) timeindex <- c(timeindex, 1:(TT-T0[i]))
  if(addTimeTrend == TRUE) X <- cbind(timeindex, X)
  
  u <- paramp0$delta[treated_idx] - X%*%paramp0$phi_delta
  
  paramp0$sigma2_eta <- 1/rgamma(1, N_obs/2 + 0.001, sum(u^2)/2 + 0.001)
  return(paramp0)
}

###### Step 2-1
# (a)
draw_beta_y0 <- function(dataY, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx
  
  dat <- dataY$dat[ctrl_idx, ]
  X <- cbind(as.matrix(dataY$Xp)[ctrl_idx, ], dataY$Xq[ctrl_idx, ]) |> as.matrix()
  
  alpha <- paramy0$alpha_i
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- as.matrix(alpha[rows,])
  alpha <- alpha[ctrl_idx,]
  
  xi <- paramy0$xi_t
  rows <- rep(1:nrow(xi), N)
  xi <- xi[rows,]
  xi <- xi[ctrl_idx, ]
  
  gamma <- paramy0$gamma_i
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- as.matrix(gamma[rows,])
  gamma <- gamma[ctrl_idx,]
  
  f_t <- paramy0$f_t
  rows <- rep(1:nrow(f_t), N)
  f_t <- as.matrix(f_t[rows,])
  f_t <- f_t[ctrl_idx, ]
  
  u <- dat$Y - rowSums(X*alpha + X*xi) - rowSums(as.matrix(f_t*gamma))
  
  sigma2 <- paramy0$sigma2
  
  k <- ncol(X)
  B0 <- diag(k)*1000
  
  paramy0$beta <- draw_regcoef(u, X, sigma2, B0) |> t()
  
  return(paramy0)
  
}

## (b-0) draw individual intercept
draw_individual_intercept_y0_overparam <- function(dataY, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx
  
  dat <- dataY$dat
  X <- cbind(dataY$Xp, dataY$Xq)
  k <- ncol(X)
  k_intercept <- 1
  k_ <- k - 1
  
  beta <- paramy0$beta
  
  intercept_i <- vector(mode = "numeric", length = N)
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT)  
    dat_i <- dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    
    X_i <- X[idx, ]
    X_i <- X_i[ctrl_idx_by_unit[[i]], ] |> as.matrix()
    X_i_intercept <- X_i[,k] |> as.matrix()
    X_i_ <- X_i[, 1:k_] |> as.matrix()
    
    alpha_i_ <- paramy0$alpha_i[, 1:k_]
    alpha_i_ <- alpha_i_[i,]
    alpha_ <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i_), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    
    xi_t <- paramy0$xi_t[ctrl_idx_by_unit[[i]],]
    gamma <- paramy0$gamma_i[i,]
    gamma <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), gamma), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    f_t <- matrix(paramy0$f_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    
    u_i <- dat_i$Y - X_i%*%beta - rowSums(X_i_*alpha_) - rowSums(X_i*xi_t) - rowSums(f_t*gamma)
    
    sigma2 <- paramy0$sigma2
    b0 = as.numeric(paramy0$mu_alpha_i[k])
    B0 = paramy0$Sigma_alpha_i[k,k]
    intercept_i[i] <- draw_regcoef_overparam(u_i, X_i_intercept, sigma2, b0, B0)
  }
  
  mu_intercept <- draw_regcoef(y = intercept_i, X = rep(1, N), sigma2 = paramy0$Sigma_alpha_i[k,k], B0 = 1000)  
  
  u <- intercept_i - c(mu_intercept)
  
  a1 <- N/2 + 0.001
  a2 <- sum(u^2)/2 + 0.001
  Sigma_intercept <- 1/rgamma(1, a1, a2) 
  
  
  res_list = list(intercept_i = intercept_i,
                  mu_intercept = mu_intercept,
                  Sigma_intercept = Sigma_intercept)  
  
  return(res_list)
}

# (b)
draw_alpha_y0_i <- function(dataY, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx
  
  
  dat <- dataY$dat
  X <- cbind(dataY$Xp, dataY$Xq)
  k <- ncol(X)
  B0 <- diag(k)*1000
  
  beta <- paramy0$beta
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT)  
    dat_i <- dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    X_i <- X[idx, ]
    X_i <- X_i[ctrl_idx_by_unit[[i]], ]
    xi_t <- paramy0$xi_t[ctrl_idx_by_unit[[i]],]
    gamma <- paramy0$gamma_i[i,]
    gamma <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), gamma), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    f_t <- matrix(paramy0$f_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    
    u_i <- dat_i$Y - X_i%*%beta - rowSums(X_i*xi_t) - rowSums(f_t*gamma)
    sigma2 <- paramy0$sigma2
    
    paramy0$alpha_i[i,] <- draw_regcoef(u_i, X_i, sigma2, B0)
  }
  return(paramy0)
}
draw_alpha_y0_i_overparam <- function(dataY, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx
  
  dat <- dataY$dat
  X <- cbind(dataY$Xp, dataY$Xq)
  k <- ncol(X)
  
  beta <- paramy0$beta
  
  alpha_i <- matrix(0, nrow = N, ncol = k-1)
  mu_alpha <- vector(mode = "numeric", length = k-1)
  Sigma_alpha <- vector(mode = "numeric", length = k-1)
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT)  
    dat_i <- dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    X_i <- X[idx, ]
    X_i <- X_i[ctrl_idx_by_unit[[i]], ] |> as.matrix()
    
    X_i_for_alpha <- X_i[,-k]
    
    alpha_i_for_intercept <- paramy0$alpha_i[i,k]
    alpha_i_for_intercept <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i_for_intercept), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    
    xi_t <- paramy0$xi_t[ctrl_idx_by_unit[[i]],]
    gamma <- paramy0$gamma_i[i,]
    gamma <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), gamma), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    f_t <- matrix(paramy0$f_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    
    u_i <- dat_i$Y - X_i%*%beta - alpha_i_for_intercept - rowSums(X_i*xi_t) - rowSums(f_t*gamma)
    
    sigma2 <- paramy0$sigma2
    b0 = as.numeric(paramy0$mu_alpha_i[-k])
    B0 = paramy0$Sigma_alpha_i[-k,-k]
    alpha_i[i,] <- draw_regcoef_overparam(u_i, X_i_for_alpha, sigma2, b0, B0)
  }
  
  nvar <- ncol(paramy0$alpha_i) - 1  ## because intercept is not estimated here
  
  for (j in 1:nvar) {
    mu_alpha[j] <- draw_regcoef(y = alpha_i[,j], X = rep(1, N), sigma2 = paramy0$Sigma_alpha_i[j,j], B0 = 1000)  
    
    u <- alpha_i[,j] - mu_alpha[j]
    
    a1 <- N/2 + 0.001
    a2 <- sum(u^2)/2 + 0.001
    Sigma_alpha[j] <- 1/rgamma(1, a1, a2) 
  }
  
  res_list = list(alpha_i = alpha_i,
                  mu_alpha = mu_alpha,
                  Sigma_alpha = Sigma_alpha)
  
  return(res_list)
}

# (c)
draw_gamma_y0_i <- function(dataY, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx

  dat <- dataY$dat
  X_for_gamma <- paramy0$f_t
  k <- ncol(X_for_gamma)
  B0 <- paramy0$sigma2*paramy0$tau2*diag(k)
  
  X <- cbind(dataY$Xp, dataY$Xq) |> as.matrix()
  beta <- paramy0$beta
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT) 
    dat_i <- dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    X_i <- X[idx, ]
    X_i <- X_i[ctrl_idx_by_unit[[i]], ] |> as.matrix()
    alpha_i <- paramy0$alpha_i[i, ]
    alpha_i <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    xi_t <- matrix(paramy0$xi_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    
    u_i <- dat_i$Y - X_i%*%beta - rowSums(X_i*alpha_i) - rowSums(X_i*xi_t)
    
    X_for_gamma_i <- X_for_gamma[ctrl_idx_by_unit[[i]],]
    sigma2 <- paramy0$sigma2
    
    paramy0$gamma_i[i,] <- draw_regcoef(u_i, X_for_gamma_i, sigma2, B0)
  }
  return(paramy0)
}
draw_gamma_y0_i_hs <- function(dataY, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx
  
  dat <- dataY$dat
  X_for_gamma <- paramy0$f_t
  k <- ncol(X_for_gamma)
  B0 <- paramy0$sigma2*paramy0$tau2*diag(k)
  
  X <- cbind(dataY$Xp, dataY$Xq) |> as.matrix()
  beta <- paramy0$beta
  
  for(i in 1:N) {
    idx <- seq((i-1)*TT + 1, i*TT) 
    dat_i <- dat[idx, ]
    dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
    X_i <- as.matrix(X[idx, ])
    X_i <- X_i[ctrl_idx_by_unit[[i]], ] |> as.matrix()
    alpha_i <- paramy0$alpha_i[i, ]
    alpha_i <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
    xi_t <- matrix(paramy0$xi_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
    
    u_i <- dat_i$Y - X_i%*%beta - rowSums(X_i*alpha_i) - rowSums(X_i*xi_t)
    
    X_for_gamma_i <- X_for_gamma[ctrl_idx_by_unit[[i]],]
    sigma2 <- paramy0$sigma2
    tau <- paramy0$tau[i]
    lambda <- paramy0$lambda[i,]
    
    res <- horseshoe(y = u_i, X = X_for_gamma_i, Sigma2 = sigma2, tau = tau, lambda = lambda)
    paramy0$gamma_i[i,] <- res$Beta
    paramy0$tau[i] <- res$tau
    paramy0$lambda[i,] <- res$lambda
    
  }
  return(paramy0)
}

# (d)
draw_xi_f_y0_t <- function(dataY, paramy0, estimate_timevarying_coefs) {
  ctrl_ids <- dataY$control_unit_ids
  treated_ids <- dataY$treated_unit_ids
  ctrl_idx <- which(dataY$dat$treat == 0)
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  TT <- dataY$TT
  
  dat <- dataY$dat 
  
  k_y <- length(paramy0$beta) 
  r_y <- ncol(paramy0$f_t)
  k <- k_y + r_y
  m0 <- rep(0, k)
  C0 <- diag(k)
  
  X <- cbind(as.matrix(dataY$Xp)[ctrl_idx,], dataY$Xq[ctrl_idx,]) |> as.matrix()
  
  beta <- paramy0$beta
  
  alpha <- paramy0$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  gamma <- as.matrix(paramy0$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  u <- (dat$Y[ctrl_idx] - X%*%beta - rowSums(X*alpha))  |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  Z <- cbind(X, gamma)  # F
  W <- diag(c(diag(paramy0$sigma2e), rep(1,  r_pl  )))
  Phi <- diag(   c(diag(paramy0$phi_xi), diag(paramy0$phi_f)   )  )  # G

  if (length(paramy0$phi_f == 1)) paramy0$phi_f <- as.matrix(paramy0$phi_f)
  V <- paramy0$sigma2*diag(N_co)   #V
  
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ]
  
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,k,TT)) 
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  paramy0$xi_t <- t(res$theta)[, 1:k_y]
  paramy0$f_t <- t(res$theta)[, (k_y+1):(k_y+r_y)]
  
  return(paramy0)
}
draw_xi_y0_t <- function(dataY, paramy0) {
  ctrl_ids <- dataY$control_unit_ids
  treated_ids <- dataY$treated_unit_ids
  ctrl_idx <- which(dataY$dat$treat == 0)
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  TT <- dataY$TT
  
  dat <- dataY$dat 
  
  k_y <- length(paramy0$beta) 
  r_y <- ncol(paramy0$f_t)
  k <- k_y + r_y
  m0 <- rep(0, k_y - 1)  # -1 because intercept is removed
  C0 <- diag(k_y - 1)  # -1 because intercept is removed
  
  X <- cbind(as.matrix(dataY$Xp)[ctrl_idx,], dataY$Xq[ctrl_idx,]) |> as.matrix()

  beta <- paramy0$beta

  alpha <- paramy0$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]

  gamma <- as.matrix(paramy0$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  f_t <- as.matrix(paramy0$f_t)
  rows <- rep(1:nrow(f_t), N_co)
  f_t <- f_t[rows,]
  
  u <- (dat$Y[ctrl_idx] - X%*%beta - rowSums(X*alpha)  - rowSums(gamma*f_t)  )  |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  ncol_X <- ncol(X)
  Z <- X[,-ncol_X]  # F  # to remove intercept
  W <- paramy0$sigma2e[-ncol_X, -ncol_X]
  Phi <- paramy0$phi_xi[-ncol_X, -ncol_X]  # G
  
  if (length(paramy0$phi_f == 1)) paramy0$phi_f <- as.matrix(paramy0$phi_f)
  V <- paramy0$sigma2*diag(N_co)   #V
  
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ]
  
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,k_y - 1,TT))   # -1 because intercept is removed
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  paramy0$xi_t <- t(res$theta)
  
  return(paramy0)
}
draw_xi_y0_t_with_intercept <- function(dataY, paramy0) {
  ctrl_ids <- dataY$control_unit_ids
  treated_ids <- dataY$treated_unit_ids
  ctrl_idx <- which(dataY$dat$treat == 0)
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  TT <- dataY$TT
  
  dat <- dataY$dat 
  
  k_y <- length(paramy0$beta) 
  r_y <- ncol(paramy0$f_t)
  k <- k_y + r_y
  m0 <- rep(0, k_y)
  C0 <- diag(k_y)
  
  X <- cbind(as.matrix(dataY$Xp)[ctrl_idx,], dataY$Xq[ctrl_idx,]) |> as.matrix()
  
  beta <- paramy0$beta
  
  alpha <- paramy0$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  gamma <- as.matrix(paramy0$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  f_t <- as.matrix(paramy0$f_t)
  rows <- rep(1:nrow(f_t), N_co)
  f_t <- f_t[rows,]
  
  u <- (dat$Y[ctrl_idx] - X%*%beta - rowSums(X*alpha)  - rowSums(gamma*f_t)  )  |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  Z <- X # F
  W <- paramy0$sigma2e
  Phi <- paramy0$phi_xi  # G
  
  if (length(paramy0$phi_f == 1)) paramy0$phi_f <- as.matrix(paramy0$phi_f)
  V <- paramy0$sigma2*diag(N_co)   #V
  
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ]
  
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,k_y,TT)) 
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  paramy0$xi_t <- t(res$theta)
  
  return(paramy0)
}
draw_xi_y0_t_intercept_only <- function(dataY, paramy0) {
  ctrl_ids <- dataY$control_unit_ids
  treated_ids <- dataY$treated_unit_ids
  ctrl_idx <- which(dataY$dat$treat == 0)
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  TT <- dataY$TT
  
  dat <- dataY$dat 
  
  k_y <- length(paramy0$beta) 
  r_y <- ncol(paramy0$f_t)
  k <- k_y + r_y
  m0 <- 0 |> as.matrix()
  C0 <- 1 |> as.matrix()
  
  X <- cbind(as.matrix(dataY$Xp)[ctrl_idx,], dataY$Xq[ctrl_idx,]) |> as.matrix()
  
  beta <- paramy0$beta
  
  alpha <- paramy0$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  gamma <- as.matrix(paramy0$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  f_t <- as.matrix(paramy0$f_t)
  rows <- rep(1:nrow(f_t), N_co)
  f_t <- f_t[rows,]
  
  u <- (dat$Y[ctrl_idx] - X%*%beta - rowSums(X*alpha)  - rowSums(gamma*f_t)  )  |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  ncol_X <- ncol(X)
  Z <- X[, ncol_X] |> matrix(nrow = nrow(X)) # F
  W <- paramy0$sigma2e[ncol_X, ncol_X]
  Phi <- paramy0$phi_xi[ncol_X, ncol_X]  # G
  
  if (length(paramy0$phi_f == 1)) paramy0$phi_f <- as.matrix(paramy0$phi_f)
  V <- paramy0$sigma2*diag(N_co)   #V
  
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ] |> as.matrix()
  
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,1,TT))   # 1 because only intercept is included
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  paramy0$xi_t <- t(res$theta)
  
  return(paramy0)
}

draw_f_y0_t <- function(dataY, paramy0) {
  ctrl_ids <- dataY$control_unit_ids
  treated_ids <- dataY$treated_unit_ids
  ctrl_idx <- which(dataY$dat$treat == 0)
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  TT <- dataY$TT
  
  dat <- dataY$dat 
  
  k_y <- length(paramy0$beta) 
  r_y <- ncol(paramy0$f_t)
  k <- k_y + r_y
  m0 <- rep(0, r_y)
  C0 <- diag(r_y)
  
  X <- cbind(as.matrix(dataY$Xp)[ctrl_idx,], dataY$Xq[ctrl_idx,]) |> as.matrix()
  
  beta <- paramy0$beta
  
  alpha <- paramy0$alpha_i[ctrl_ids,] 
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  xi <- paramy0$xi_t
  rows <- rep(1:nrow(xi), N_co)
  xi <- xi[rows,]
  
  gamma <- as.matrix(paramy0$gamma_i[ctrl_ids,])
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  u <- (dat$Y[ctrl_idx] - X%*%beta - rowSums(X*alpha) -rowSums(X*xi) )  |>  matrix(nrow = TT, ncol = N_co) |> t() #Y (N_co times TT)-by-1
  
  Z <- gamma  # F
  W <- diag(r_y)
  Phi <- paramy0$phi_f  # G
  
  if (length(paramy0$phi_f == 1)) paramy0$phi_f <- as.matrix(paramy0$phi_f)
  V <- paramy0$sigma2*diag(N_co)   #V
  
  rows <- NULL
  for(t in 1:TT) rows <- c(rows, seq(from = t, to = N_co*TT, by = TT))
  Z2 <- Z[rows, ]
  
  rows <- NULL
  Z3 <- array(numeric(),c(N_co,r_y,TT)) 
  for(t in 1:TT) Z3[,,t] <- Z2[((t-1)*N_co + 1):(N_co*t), ]
  
  res <- ffbs(m0, C0, Y = u, F = Z3, G = Phi, V = V, W = W, N = N_co, TT = TT)
  
  paramy0$f_t <- t(res$theta)
  
  return(paramy0)
}

# (e)
draw_phi_xi_y0_j <- function(dataY, paramy0) {
  param <- paramy0
  J <- ncol(param$xi_t)
  
  for(j in 1:J) {
    y <- param$xi_t[,j]
    X <- c(0, y[1:(length(y) - 1)])
    B0 <- 1000
    sigma2e <- param$sigma2e[j,j]
    
    paramy0$phi_xi[j, j] <- draw_regcoef(y, X, sigma2e, B0)
  }
  return(paramy0)
}

# (f)
draw_phi_f_y0_j <- function(dataY, paramy0) {
  param <- paramy0
  J <- ncol(param$f_t)
  
  for(j in 1:J) {
    y <- param$f_t[,j]
    X <- c(0, y[1:(length(y) - 1)])
    B0 <- 1000
    sigma2f <- 1
    
    paramy0$phi_f[j, j] <- draw_regcoef(y, X, sigma2f, B0)
  }
  return(paramy0)
}

# (g)
draw_sigma2_e_y0_j <- function(dataY, paramy0) {
  TT <- dataY$TT

  param <- paramy0
  J <- ncol(param$xi_t)
  
  for(j in 1:J) {
    y <- param$xi_t[,j]
    X <- c(0, y[1:(length(y) - 1)])
    u <- y - param$phi_xi[j,j]*X
    paramy0$sigma2e[j,j] <- 1/rgamma(1, TT/2 + 0.001, sum(u^2)/2 + 0.001)
  }
  return(paramy0)
}

# (h)
draw_sigma2_eps_y0 <- function(dataY, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx
  N_obs <- length(ctrl_idx)
  
  dat <- dataY$dat
  X <- cbind(as.matrix(dataY$Xp)[ctrl_idx, ], dataY$Xq[ctrl_idx, ]) |> as.matrix()
  beta <- paramy0$beta
  
  alpha <- paramy0$alpha_i
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  alpha <- alpha[ctrl_idx,]
  
  xi <- paramy0$xi_t
  rows <- rep(1:nrow(xi), N)
  xi <- xi[rows,]
  xi <- xi[ctrl_idx, ]
  
  gamma <- paramy0$gamma_i
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- as.matrix(gamma[rows,])
  gamma <- as.matrix(gamma[ctrl_idx,])
  
  f_t <- paramy0$f_t
  rows <- rep(1:nrow(f_t), N)
  f_t <- as.matrix(f_t[rows,])
  f_t <- as.matrix(f_t[ctrl_idx, ])
  
  u <- dat$Y[ctrl_idx] - X%*%beta - rowSums(X*alpha + X*xi) - rowSums(f_t*gamma)
  
  paramy0$sigma2 <- 1/rgamma(1, N_obs/2 + 0.001, sum(u^2)/2 + 0.001)
  
  return(paramy0)
}

# (i)
draw_pi_y0_j <- function(dataY, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx
  
  param <- paramy0
  J <- ncol(param$f_t)
  
  theta_y0 <- param$theta
  sigma2_eps <- param$sigma2
  tau2 <- param$tau2
  
  dat <- dataY$dat
  X <- cbind(dataY$Xp, dataY$Xq)
  beta <- paramy0$beta
  
  for (j in 1:J) {
    
    A1 <- theta_y0*(sigma2_eps*tau2)^(-N/2)
    
    tmp1 <- tmp2 <- rep(0, N)
    
    for (i in 1:N) {
      idx <- seq((i-1)*TT + 1, i*TT) 
      dat_i <- dat[idx, ]
      dat_i <- dat_i[ctrl_idx_by_unit[[i]], ]
      X_i <- as.matrix(X[idx, ])
      X_i <- X_i[ctrl_idx_by_unit[[i]], ]
      
      alpha_i <- param$alpha_i[i, ]
      alpha_i <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), alpha_i), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
      xi_t <- matrix(param$xi_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
      gamma_i <- param$gamma_i[i,]
      gamma_i <- matrix(replicate(length(ctrl_idx_by_unit[[i]]), gamma_i), byrow = TRUE, nrow = length(ctrl_idx_by_unit[[i]]))  # matrix
      f_t <- matrix(param$f_t[ctrl_idx_by_unit[[i]],], nrow = length(ctrl_idx_by_unit[[i]]))
      
      z <- dat_i$Y - X_i%*%beta - rowSums(X_i*alpha_i + X_i*xi_t) - rowSums(as.matrix(f_t[,-j]*gamma_i[,-j]))
      cond_var_i <- (  sum(f_t[,j]^2) +  1/tau2 )
      
      tmp1[i] <- sum(f_t[,j]*z)^2  /  cond_var_i  
      tmp2[i] <- sqrt(sigma2_eps/cond_var_i )

    }
    
    one_minus_mu <- (1 - theta_y0) / (  A1* exp(1/(2*sigma2_eps)*sum(tmp1))*prod(tmp2) + (1 - theta_y0)  )
    mu <- 1 - one_minus_mu
    
    paramy0$pi[j] <- rbinom(1, size = 1, prob = mu)
  }
  
  # set gamma = 0 for pi = 0
  paramy0$gamma_i[,which(paramy0$pi == 0)] <- 0
  
  return(paramy0)
}

# (j)
draw_theta_y0 <- function(dataY, paramy0) {
  param <- paramy0
  b1 <- 1 + sum(param$pi)
  b2 <- 1 + sum(1 - param$pi)
  paramy0$theta <- rbeta(1, b1, b2)
  return(paramy0)
}

# (k)
draw_tau2_y0 <- function(dataY, paramy0) {
  N_co <- dataY$N_co
  N <- dataY$N
  
  param <- paramy0
  pi <- param$pi
  sigma2_eps <- param$sigma2
  gamma <- param$gamma_i
  s <- param$s
  
  a1 <- 1/2 + sum(pi)*N/2
  a2 <- s/2 + sum(gamma^2)/(2*sigma2_eps)
  
  paramy0$tau2 <- 1/rgamma(1, a1, a2)
  return(paramy0)

}

# (l)
draw_s_y0 <- function(dataY, paramy0) {
  param <- paramy0
  tau2 <- param$tau2
  paramy0$s <- 1/rgamma(1, 0.01 + 1/2, 0.01 + 1/tau2)
  return(paramy0)
}

###### Step 2-2
draw_y0_mis <- function(dataY, paramp0, paramy0) {
  TT <- dataY$TT
  N <- dataY$N
  N_co <- dataY$N_co
  N_tr <- dataY$N_tr
  T0 <- dataY$T0
  k_y1 <- dataY$k_y1
  treated_ids <- dataY$treated_unit_ids
  ctrl_ids <- dataY$control_unit_ids
  treated_idx_by_unit <- dataY$treated_idx_by_unit
  ctrl_idx_by_unit <- dataY$ctrl_idx_by_unit
  treated_idx <- dataY$treated_idx
  ctrl_idx <- dataY$ctrl_idx
  
  Xp0_mis <- matrix(0, nrow = N*TT, ncol = k_y1)
  
  if(k_y1 > 0) for (l in 1:k_y1) Xp0_mis[,l] <- paramp0[[l]]$p0_mis
  
  X <- cbind(Xp0_mis, dataY$Xq) |> as.matrix()
  
  beta <- paramy0$beta
  
  alpha <- paramy0$alpha_i
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- alpha[rows,]
  
  xi <- paramy0$xi_t
  rows <- rep(1:nrow(xi), N)
  xi <- xi[rows,]
  
  gamma <- paramy0$gamma_i
  rows <- rep(1:nrow(gamma), each = TT)
  gamma <- gamma[rows,]
  
  f_t <- paramy0$f_t
  rows <- rep(1:nrow(f_t), N)
  f_t <- f_t[rows,]
  
  sigma2 <- paramy0$sigma2
  
  mu <- X%*%beta +  rowSums(X*alpha + X*xi) + rowSums(f_t*gamma)
  
  res <- rnorm(n = N*TT, mean = mu, sd = sqrt(sigma2))
  #res[ctrl_idx] <- NA
  
  paramy0$y0_mis <- res
    
  return(paramy0)
}

##### Step 3 Decomposition and Attribution
# (a) draw delta
draw_y0_delta <- function(dataP, dataY, paramp0, paramy0){
  N <- dataY$N
  TT <- dataY$TT
  X_obs <- cbind(dataY$Xp, dataY$Xq)

  Xp_imputed <- as.matrix(dataY$Xp)
  k_y1 <- ncol(Xp_imputed)
  for(l in 1:k_y1) Xp_imputed[,l] <- paramp0[[l]]$p0_mis
  X_imputed <- cbind(Xp_imputed, dataY$Xq)
  
  alpha <- paramy0$alpha_i
  rows <- rep(1:nrow(alpha), each = TT)
  alpha <- as.matrix(alpha[rows,])
  
  xi <- paramy0$xi_t
  rows <- rep(1:nrow(xi), N)
  xi <- xi[rows,]
    
  paramy0$tte <-  dataY$dat$Y - paramy0$y0_mis
  X_diff <- X_obs - X_imputed
  X_diff <- as.matrix(X_diff)
  paramy0$delta <- paramy0$tte - X_diff%*%paramy0$beta - rowSums(X_diff*alpha + X_diff*xi)
  return(paramy0)
}

# (b) draw phi y
draw_phi_delta_y <- function(dataY, paramy0, addTimeTrend = 1) {
  TT <- dataY$TT
  T0 <- dataY$T0
  N_tr <- dataY$N_tr
  treated_idx <- dataY$treated_idx
  
  # sigma2_eta <- paramy0$sigma2_eta
  sigma2_eta <- 2*paramy0$sigma2
  X <- dataY$Xdelta[treated_idx, ]
  
  timeindex <- vector(mode = "numeric")
  for(i in 1:N_tr) timeindex <- c(timeindex, 1:(TT-T0[i])   )
  if(addTimeTrend == 1) X <- cbind(timeindex, X)
    
  u <- paramy0$delta[treated_idx]
  Phi0 <- 1000*diag(ncol(X))
  
  paramy0$phi_delta <- draw_regcoef(u, X, sigma2_eta, Phi0) |> t()
    
  return(paramy0)
}

# (c) draw sigma2_eta_y
draw_sigma2_eta_y <- function(dataY, paramy0, addTimeTrend = TRUE) {
  TT <- dataY$TT
  T0 <- dataY$T0
  N_tr <- dataY$N_tr
  treated_idx <- dataY$treated_idx
  
  N_obs <- length(treated_idx)
  X <- dataY$Xdelta[treated_idx, ] |> as.matrix()
   
  timeindex <- vector(mode = "numeric")
  for(i in 1:N_tr) timeindex <- c(timeindex, 1:(TT-T0[i]))
  if(addTimeTrend == TRUE) X <- cbind(timeindex, X)
  
  u <- paramy0$delta[treated_idx] - X%*%paramy0$phi_delta

  paramy0$sigma2_eta <- 1/rgamma(1, N_obs/2 + 0.001, sum(u^2)/2 + 0.001)
  return(paramy0)
}



#--------------------- Functions to generate simulation data -------------------#

simdata_gen <- function(N,                   # number of units (treatment and control)
                        N_tr,                # number of treatment units
                        TT,                  # number of time periods
                        T0_tr,               # number of pre-treatment periods for each treated unit. A vector of length N_tr
                        
                        k_y,                 # number of covariates (including the intercept) in the outcome equation (the "y" equation)
                        k_y1,                # number of covariates that vary with treatment adoption--i.e., the number of the "p" variables. Exclude intercept
                        r_y,                 # number of common factors in the outcome equation
                        beta_y,              # coefficients in the outcome eq (the "y" eq). A vector of length k_y. The first k_y1 coefficients are the coefficients for the endogenous varibles.
                        k_y_phi,             # number of variables that explain the residual treatment effect (excluding the intercept)
                        intercept_delta_y,   # the amount of level change in \delta_{y,it} after treatment adoption
                        change_rate_delta_y, # the amount of change per time period in \delta_{y,it} after treatment adoption
                        phi_y_delta,         # the coefficient of covariates that explain \delta_{y,it}, the residual effect. A vector of length k_y_phi.
                        
                        k_p,                 # number of covariates in each "p" equation (i.e., the covariate eq). A vector of length k_y1 
                        r_p,                 # number of external factors in each "p" equation (i.e., the covariate eq). A vector of length k_y1
                        beta_p,              # coefficients in each "p" equation (i.e., the covariate eq). A list of length k_y1. The length of each element in the list is determined by the corresponding element in k_p
                        intercept_delta_p,   # the amount of level change of \delta_{p,it} after treatment adoption. A vector of length k_y1
                        change_rate_delta_p, # the amount of change per time period in \delta_{p,it} after treatment adoption. A vector of length k_y1 
                        
                        simdata_filename,    # an .RData file that saves the simulated data. A character string.
                        simparam_filename    # an .RData file that saves the simulation parameters. A character string
)
{
  
  requireNamespace("tidyverse", quietly = TRUE)
  requireNamespace("mvtnorm", quietly = TRUE)
  requireNamespace("HDInterval", quietly = TRUE)
  requireNamespace("abind", quietly = TRUE)
  
  ########## Input Example: Start #######
  # N <- 50                                 # number of units (treatment and control)
  # N_tr <- 7                               # number of treatment units
  # TT <- 40                                # number of time periods
  # T0_tr <- c(25, 25, 25, 25, 25, 25, 25)  # number of pre-treatment periods for each treated unit. A vector of length N_tr
  # 
  # k_y <- 9                                # number of covariates (including the intercept, mediators, and exogenous covariates) in the Outcome Equation (the "y" equation)
  # k_y1 <- 2                               # number of mediators--i.e., the number of the "p" variables--in the Outcome Equation. 
  # r_y <- 2                                # number of latent factors in the Outcome Equation
  # beta_y <-  c(3,6,4,2,1,1,1,1,1)         # coefficients in the Outcome Equation. A vector of length k_y. The first k_y1 coefficients are the coefficients of the k_y1 mediators.
  # k_y_phi <- 5                            # number of variables that explain the direct treatment effect (excluding the intercept).
  # intercept_delta_y <- 0                  # the amount of level change in the direct effect, delta_{y,it}, after treatment adoption.
  # change_rate_delta_y <- 2                # the amount of change per time period in the direct effect, delta_{y,it}, after treatment adoption.
  # phi_y_delta <- c(1,2,3,4,5)             # the coefficient of covariates that explain the direct effect, delta_{y,it}. A vector of length k_y_phi.
  # 
  # k_p <- rep(3, k_y1)                     # number of covariates in each Mediator Equation. A vector of length k_y1. 
  # r_p <- rep(2, k_y1)                     # number of latent factors in Mediator Equation. A vector of length k_y1.
  # beta_p <- list(c(3,1,2), c(1,1,1))      # coefficients in each Mediator Equation. A list of length k_y1. The length of each element in the list should be same to the corresponding element in k_p.
  # intercept_delta_p <- c(0, 0)            # the amount of level change in delta_{p,itl}--the treatment effect on the lth mediator, after treatment adoption. A vector of length k_y1.
  # change_rate_delta_p <- c(-1, -1)        # the amount of change per time period in delta_{p,itl}--the treatment effect on the lth mediator, after treatment adoption. A vector of length k_y1.
  # 
  # 
  # simdata_filename <- "simdata00.RData"             # an .RData file that saves the simulated data. A character string.
  # simparam_filename <- "sim_true_params00.RData"    # an .RData file that saves the simulation parameters. A character string
  
  ## Note that covariates are generated randomly in the code. Also, the parameters that are not provided through the function arguments are generated in the code.
  ########## Input Example: End #######
  
  N_co <- N - N_tr                         # number of control units
  T0 <- c(T0_tr, rep(Inf, N_co))           # Inf means that the uni is a control unit
  k_y2 <- k_y - k_y1                       # number of covariates that do not vary with treatment adoption in the outcome equation
  D <- matrix(0, nrow = N, ncol = TT)      # treatment adoption matrix
  for (i in 1:N_tr) D[i, (T0_tr[i] + 1):TT] <- 1
  
  ### Generating p_itl (i = 1, 2, ..., N, t = 1, 2, ..., TT, and l = 1, 2, ..., k_y1)
  tau_pitl <- matrix(rnorm(N*TT, sd = sqrt(0.25)), nrow = N, ncol = TT)
  p_itl <- vector(mode = "list", length = k_y1)
  alpha_pil <- vector(mode = "list", length = k_y1)
  gamma_pil <- vector(mode = "list", length = k_y1)
  Phi_p_xi_l <- vector(mode = "list", length = k_y1)
  Phi_p_f_l <- vector(mode = "list", length = k_y1)
  tau_pitl <- vector(mode = "list", length = k_y1)
  
  for (l in 1:k_y1) { 
    k_pl_ <- k_p[l]
    r_pl_ <- r_p[l]
    alpha_pil[[l]] <- matrix(rnorm(N*k_pl_), nrow = N, ncol = k_pl_)
    gamma_pil[[l]] <- matrix(rnorm(N*r_pl_, 1, 1), nrow = N) 
    Phi_p_xi_l[[l]] <- rep(0, k_pl_)
    Phi_p_f_l[[l]] <- rep(0.7, r_pl_)
    tau_pitl[[l]] <- matrix(rnorm(N*TT, sd = sqrt(0.25)), nrow = N, ncol = TT)
    
    p_itl[[l]] <- generate_pitl(N, 
                                TT, 
                                N_tr, 
                                T0, 
                                D,
                                k_pl_, 
                                r_pl_,
                                beta_p[[l]],
                                alpha_pil[[l]],
                                Phi_p_xi_l[[l]],
                                Phi_p_f_l[[l]],
                                gamma_pil[[l]], 
                                tau_pitl[[l]],
                                change_rate_delta = change_rate_delta_p[l],
                                intercept_delta = intercept_delta_p[l])
  }
  
  ### Generating y_it (i = 1, 2, ..., N; t = 1, 2, ..., TT)
  alpha_yi <-  matrix(rnorm(N*k_y), nrow = N, ncol = k_y)
  gamma_yi <- matrix(rnorm(N*r_y, 1, 1), nrow = N)  
  sum_gamma_yi_order <- rowSums(gamma_yi) |> order(decreasing = TRUE)
  gamma_yi <- gamma_yi[sum_gamma_yi_order,]
  Phi_y_xi  <- rep(0, k_y)
  Phi_y_f <- rep(0.7, r_y)
  tau_yit <-  matrix(rnorm(N*TT, sd = sqrt(0.25)), nrow = N, ncol = TT)
  
  y_it <- generate_yit(N, 
                       TT, 
                       N_tr,
                       T0,
                       D, 
                       p_itl, 
                       k_y, 
                       k_y1,
                       k_y2, 
                       r_y,
                       k_y_phi,
                       beta_y,
                       alpha_yi,
                       Phi_y_xi,
                       Phi_y_f,
                       gamma_yi,
                       tau_yit,
                       phi_y_delta,
                       change_rate_delta = change_rate_delta_y,
                       intercept_delta = intercept_delta_y)
  
  
  ## converting the simulated data to a format used in estimation
  simdata <- convert2estimableData(N, 
                                   TT,
                                   T0,
                                   D,
                                   N_tr, 
                                   N_co, 
                                   k_y,
                                   k_y1,
                                   k_y2,
                                   k_y_phi,
                                   k_p,
                                   p_itl,
                                   y_it, 
                                   beta_y, 
                                   alpha_yi, 
                                   delta_pitl)
  
  
  save(simdata, file = simdata_filename)
  
  ## save parameters
  true_paramp0 <- vector(mode = "list", length = k_y1)
  for (l in 1:k_y1) {
    beta_p <- beta_p[[l]]
    alpha_p_i <- alpha_pil[[l]]
    mu_alpha_p_i <- rep(0, k_p[l])
    Sigma_alpha_p_i <- diag(k_p[l])
    xi_p_t <- p_itl[[l]]$xi_ptl
    gamma_p_i <- gamma_pil[[l]]
    f_p_t <- p_itl[[l]]$f_ptl
    sigma2_p <- 1
    phi_xi <- Phi_p_xi_l[[l]]
    phi_f <- Phi_p_f_l[[l]]
    sigma2_p_e <- diag(k_p[l])
    
    true_paramp0[[l]] <- list(beta = beta_p, alpha_i = alpha_p_i, mu_alpha_i = mu_alpha_p_i, Sigma_alpha_i = Sigma_alpha_p_i,
                              xi_t = xi_p_t, gamma_i = gamma_p_i, f_p_t = f_p_t, sigma2 = sigma2_p, 
                              sigma2e = sigma2_p_e, phi_xi = phi_xi, phi_f = phi_f)
  }
  
  
  beta_y <- beta_y
  alpha_yi <- alpha_yi
  mu_alpha_yi <- rep(0, k_y)  # overparam mean of alpha
  Sigma_alpha_yi <- diag(k_y)
  xi_yt <- y_it$xi_yt
  gamma_yi <- gamma_yi
  f_yt <- y_it$f_yt
  sigma2_y <- 1
  phi_xi <- Phi_y_xi
  phi_f <- Phi_y_f
  sigma2_y_e <- diag(k_y)
  phi_delta_y <- phi_y_delta
  sigma2_eta_y <- 1
  
  true_paramy0 <- list(beta = beta_y, alpha_i = alpha_yi, mu_alpha_i = mu_alpha_yi, Sigma_alpha_i = Sigma_alpha_yi,
                       xi_t = xi_yt, gamma_i = gamma_yi, f_t = f_yt, sigma2 = sigma2_y,
                       sigma2e = sigma2_y_e, phi_xi = phi_xi, phi_f = phi_f,
                       phi_delta = phi_delta_y, sigma2_eta = sigma2_eta_y)
  
  save(true_paramp0, true_paramy0, file = simparam_filename)
  
  cat("Simulation data were saved in the following files: (1)", simdata_filename, "; (2)", simparam_filename, "\n")
  
  res_list <-  list(data = simdata, true_param_p = true_paramp0, true_param_y = true_paramy0)
  return(res_list)
}

simdata_gen_endo_mediator <- function(N,                   # number of units (treatment and control)
                                      N_tr,                # number of treatment units
                                      TT,                  # number of time periods
                                      T0_tr,               # number of pre-treatment periods for each treated unit. A vector of length N_tr
                                      
                                      k_y,                 # number of covariates (including the intercept, mediators, and exogenous covariates) in the Outcome Equation (the "y" equation)
                                      k_y1,                # number of mediators--i.e., the number of the "p" variables--in the Outcome Equation. 
                                      r_y,                 # number of latent factors in the Outcome Equation
                                      beta_y,              # coefficients in the Outcome Equation. A vector of length k_y. The first k_y1 coefficients are the coefficients of the k_y1 mediators.
                                      k_y_phi,             # number of variables that explain the direct treatment effect (excluding the intercept).
                                      intercept_delta_y,   # the amount of level change in the direct effect, delta_{y,it}, after treatment adoption.
                                      change_rate_delta_y, # the amount of change per time period in the direct effect, delta_{y,it}, after treatment adoption.
                                      phi_y_delta,         # the coefficient of covariates that explain the direct effect, delta_{y,it}. A vector of length k_y_phi.
                                      
                                      k_p,                 # number of covariates in each Mediator Equation. A vector of length k_y1. 
                                      r_p,                 # number of latent factors in Mediator Equation. A vector of length k_y1.
                                      beta_p,              # coefficients in each Mediator Equation. A list of length k_y1. The length of each element in the list should be same to the corresponding element in k_p.
                                      intercept_delta_p,   # the amount of level change in delta_{p,itl}--the treatment effect on the lth mediator, after treatment adoption. A vector of length k_y1.
                                      change_rate_delta_p, # the amount of change per time period in delta_{p,itl}--the treatment effect on the lth mediator, after treatment adoption. A vector of length k_y1.
                                      
                                      simdata_filename,    # an .RData file that saves the simulated data. A character string.
                                      simparam_filename    # an .RData file that saves the simulation parameters. A character string.
)
{
  
  requireNamespace("tidyverse", quietly = TRUE)
  requireNamespace("mvtnorm", quietly = TRUE)
  requireNamespace("HDInterval", quietly = TRUE)
  requireNamespace("ggplot2", quietly = TRUE)
  requireNamespace("abind", quietly = TRUE)
  
  ########## Input Example: Start #######
  # N <- 50                                 # number of units (treatment and control)
  # N_tr <- 7                               # number of treatment units
  # TT <- 40                                # number of time periods
  # T0_tr <- c(25, 25, 25, 25, 25, 25, 25)  # number of pre-treatment periods for each treated unit. A vector of length N_tr
  # 
  # k_y <- 9                                # number of covariates (including the intercept, mediators, and exogenous covariates) in the Outcome Equation (the "y" equation)
  # k_y1 <- 2                               # number of mediators--i.e., the number of the "p" variables--in the Outcome Equation. 
  # r_y <- 2                                # number of latent factors in the Outcome Equation
  # beta_y <-  c(3,6,4,2,1,1,1,1,1)         # coefficients in the Outcome Equation. A vector of length k_y. The first k_y1 coefficients are the coefficients of the k_y1 mediators.
  # k_y_phi <- 5                            # number of variables that explain the direct treatment effect (excluding the intercept).
  # intercept_delta_y <- 0                  # the amount of level change in the direct effect, delta_{y,it}, after treatment adoption.
  # change_rate_delta_y <- 2                # the amount of change per time period in the direct effect, delta_{y,it}, after treatment adoption.
  # phi_y_delta <- c(1,2,3,4,5)             # the coefficient of covariates that explain the direct effect, delta_{y,it}. A vector of length k_y_phi.
  # 
  # k_p <- rep(3, k_y1)                     # number of covariates in each Mediator Equation. A vector of length k_y1. 
  # r_p <- rep(2, k_y1)                     # number of latent factors in Mediator Equation. A vector of length k_y1.
  # beta_p <- list(c(3,1,2), c(1,1,1))      # coefficients in each Mediator Equation. A list of length k_y1. The length of each element in the list should be same to the corresponding element in k_p.
  # intercept_delta_p <- c(0, 0)            # the amount of level change in delta_{p,itl}--the treatment effect on the lth mediator, after treatment adoption. A vector of length k_y1.
  # change_rate_delta_p <- c(-1, -1)        # the amount of change per time period in delta_{p,itl}--the treatment effect on the lth mediator, after treatment adoption. A vector of length k_y1.
  # 
  # simdata_filename <- "simdata00.RData"             # an .RData file that saves the simulated data. A character string.
  # simparam_filename <- "sim_true_params00.RData"    # an .RData file that saves the simulation parameters. A character string
  
  ## Note that covariates are generated randomly in the code. Also, the parameters that are not provided through the function arguments are generated in the code.
  ########## Input Example: End #######
  
  N_co <- N - N_tr                         # number of control units
  T0 <- c(T0_tr, rep(Inf, N_co))           # Inf means that the uni is a control unit
  k_y2 <- k_y - k_y1                       # number of covariates that do not vary with treatment adoption in the outcome equation
  D <- matrix(0, nrow = N, ncol = TT)      # treatment adoption matrix
  for (i in 1:N_tr) D[i, (T0_tr[i] + 1):TT] <- 1
  
  ### Generating p_itl (i = 1, 2, ..., N, t = 1, 2, ..., TT, and l = 1, 2, ..., k_y1)
  tau_pitl <- matrix(rnorm(N*TT, sd = sqrt(0.25)), nrow = N, ncol = TT)
  p_itl <- vector(mode = "list", length = k_y1)
  alpha_pil <- vector(mode = "list", length = k_y1)
  gamma_pil <- vector(mode = "list", length = k_y1)
  Phi_p_xi_l <- vector(mode = "list", length = k_y1)
  Phi_p_f_l <- vector(mode = "list", length = k_y1)
  tau_pitl <- vector(mode = "list", length = k_y1)
  
  for (l in 1:k_y1) { 
    k_pl_ <- k_p[l]
    r_pl_ <- r_p[l]
    alpha_pil[[l]] <- matrix(rnorm(N*k_pl_), nrow = N, ncol = k_pl_)
    gamma_pil[[l]] <- matrix(rnorm(N*r_pl_, 1, 1), nrow = N) 
    Phi_p_xi_l[[l]] <- rep(0, k_pl_)
    Phi_p_f_l[[l]] <- rep(0.7, r_pl_)
    tau_pitl[[l]] <- matrix(rnorm(N*TT, sd = sqrt(0.25)), nrow = N, ncol = TT)
    
    p_itl[[l]] <- generate_pitl(N, 
                                TT, 
                                N_tr, 
                                T0, 
                                D,
                                k_pl_, 
                                r_pl_,
                                beta_p[[l]],
                                alpha_pil[[l]],
                                Phi_p_xi_l[[l]],
                                Phi_p_f_l[[l]],
                                gamma_pil[[l]], 
                                tau_pitl[[l]],
                                change_rate_delta = change_rate_delta_p[l],
                                intercept_delta = intercept_delta_p[l])
  }
  
  ### Generating y_it (i = 1, 2, ..., N; t = 1, 2, ..., TT)
  alpha_yi <-  matrix(rnorm(N*k_y), nrow = N, ncol = k_y)
  gamma_yi <- matrix(rnorm(N*r_y, 1, 1), nrow = N)  
  sum_gamma_yi_order <- rowSums(gamma_yi) |> order(decreasing = TRUE)
  gamma_yi <- gamma_yi[sum_gamma_yi_order,]
  Phi_y_xi  <- rep(0, k_y)
  Phi_y_f <- rep(0.7, r_y)
  tau_yit <-  matrix(rnorm(N*TT, sd = sqrt(0.25)), nrow = N, ncol = TT)
  
  y_it <- generate_yit_endo_mediator(N, 
                                   TT, 
                                   N_tr,
                                   T0,
                                   D, 
                                   p_itl, 
                                   k_y, 
                                   k_y1,
                                   k_y2, 
                                   r_y,
                                   k_y_phi,
                                   beta_y,
                                   alpha_yi,
                                   Phi_y_xi,
                                   Phi_y_f,
                                   gamma_yi,
                                   tau_yit,
                                   phi_y_delta,
                                   change_rate_delta = change_rate_delta_y,
                                   intercept_delta = intercept_delta_y)
  
  ##### compute and save the unobserved part  ###
  
  ## converting the simulated data to a format used in estimation
  simdata <- convert2estimableData(N, 
                                   TT,
                                   T0,
                                   D,
                                   N_tr, 
                                   N_co, 
                                   k_y,
                                   k_y1,
                                   k_y2,
                                   k_y_phi,
                                   k_p,
                                   p_itl,
                                   y_it, 
                                   beta_y, 
                                   alpha_yi, 
                                   delta_pitl)
  
  
  save(simdata, file = simdata_filename)
  
  ## save parameters
  true_paramp0 <- vector(mode = "list", length = k_y1)
  for (l in 1:k_y1) {
    beta_p <- beta_p[[l]]
    alpha_p_i <- alpha_pil[[l]]
    mu_alpha_p_i <- rep(0, k_p[l])
    Sigma_alpha_p_i <- diag(k_p[l])
    xi_p_t <- p_itl[[l]]$xi_ptl
    gamma_p_i <- gamma_pil[[l]]
    f_p_t <- p_itl[[l]]$f_ptl
    sigma2_p <- 1
    phi_xi <- Phi_p_xi_l[[l]]
    phi_f <- Phi_p_f_l[[l]]
    sigma2_p_e <- diag(k_p[l])
    
    true_paramp0[[l]] <- list(beta = beta_p, alpha_i = alpha_p_i, mu_alpha_i = mu_alpha_p_i, Sigma_alpha_i = Sigma_alpha_p_i,
                              xi_t = xi_p_t, gamma_i = gamma_p_i, f_p_t = f_p_t, sigma2 = sigma2_p, 
                              sigma2e = sigma2_p_e, phi_xi = phi_xi, phi_f = phi_f)
  }
  
  
  beta_y <- beta_y
  alpha_yi <- alpha_yi
  mu_alpha_yi <- rep(0, k_y)  # overparam mean of alpha
  Sigma_alpha_yi <- diag(k_y)
  xi_yt <- y_it$xi_yt
  gamma_yi <- gamma_yi
  f_yt <- y_it$f_yt
  sigma2_y <- 1
  phi_xi <- Phi_y_xi
  phi_f <- Phi_y_f
  sigma2_y_e <- diag(k_y)
  phi_delta_y <- phi_y_delta
  sigma2_eta_y <- 1
  
  true_paramy0 <- list(beta = beta_y, alpha_i = alpha_yi, mu_alpha_i = mu_alpha_yi, Sigma_alpha_i = Sigma_alpha_yi,
                       xi_t = xi_yt, gamma_i = gamma_yi, f_t = f_yt, sigma2 = sigma2_y,
                       sigma2e = sigma2_y_e, phi_xi = phi_xi, phi_f = phi_f,
                       phi_delta = phi_delta_y, sigma2_eta = sigma2_eta_y)
  
  ## unobserved part of p_itl
  unobserved_p <- matrix(rep(0, N*TT*k_y1), ncol = k_y1)
  
  for(l in 1:k_y1) {
    for(i in 1:N) {
      tmp_ <- rowSums(p_itl[[l]]$f_ptl*t(matrix( rep( p_itl[[l]]$gamma_pil[i,], TT)  , nrow = r_p[l])))
      unobserved_p[((i-1)*TT + 1):(i*TT), l] <-  tmp_
    }
    unobserved_p[,l] <- unobserved_p[,l] + as.vector(p_itl[[l]]$epsilon_pitl)
  }
  
  ## unobserved part of y_it
  unobserved_y = rep(0, N*TT)
  for(i in 1:N) {
    tmp_ <- rowSums(y_it$f_yt*t( matrix(  rep(  y_it$gamma_yi[i,], TT   ), nrow = r_y )    ))
    unobserved_y[((i-1)*TT + 1):(i*TT) ] <- tmp_
  }
  
  unobserved_y <- unobserved_y + as.vector(y_it$epsilon_yit)
  
  save(true_paramp0, true_paramy0, unobserved_p, unobserved_y, file = simparam_filename)
  
  cat("Simulation data were saved in the following files: (1)", simdata_filename, "; (2)", simparam_filename, "\n")
  
  
  res_list <-  list(data = simdata, true_param_p = true_paramp0, true_param_y = true_paramy0, 
                    unobserved_p = unobserved_p, unobserved_y = unobserved_y)
  return(res_list)
}

generate_pitl <- function(N, 
                          TT, 
                          N_tr, 
                          T0, 
                          D,
                          k_pl_, 
                          r_pl_,
                          beta_pl,
                          alpha_pil,
                          Phi_p_xi_l,
                          Phi_p_f_l,
                          gamma_pil, 
                          tau_pitl,
                          change_rate_delta,
                          intercept_delta) {

  x_pitl <- rnorm(N*TT*k_pl_) |> array(dim = c(N, TT, k_pl_))
  
  xi_ptl <- matrix(0, TT, k_pl_)
  for(t in 2:TT) for(j in 1:k_pl_) xi_ptl[t,j] <-  Phi_p_xi_l[j]*xi_ptl[t-1,j] + rnorm(1)
  
  f_ptl <- matrix(0, TT, r_pl_)
  for (t in 2:TT) for (j in 1:r_pl_) f_ptl[t,j] <- Phi_p_f_l[j]*f_ptl[t-1,j] + rnorm(1)

  delta_pitl <- matrix(0, nrow = N, ncol = TT)
  for (i in 1:N_tr) for (t in (T0[i]+1):TT) delta_pitl[i, t] <- intercept_delta + change_rate_delta*(t - T0[i]) + tau_pitl[i, t]  
  
  epsilon_pitl <- matrix(rnorm(N*TT), nrow = N, ncol = TT)
  p_itl <- p0_itl <- p1_itl <- matrix(0, nrow = N, ncol = TT)
  for (i in 1:N) for (t in 1:TT) {
    p0_itl[i,t] <- sum(x_pitl[i,t,]*beta_pl) + sum(x_pitl[i,t,]*alpha_pil[i, ]) + sum(x_pitl[i,t,]*xi_ptl[t,]) + sum(gamma_pil[i,]*f_ptl[t,]) + epsilon_pitl[i,t]
    p1_itl[i,t] <- p0_itl[i,t] + delta_pitl[i,t]
  }
  
  p_itl <- p0_itl*(1-D) + p1_itl*D
  
  res <- list(p0_itl = p0_itl, p1_itl = p1_itl, delta_pitl = delta_pitl, p_itl = p_itl, x_pitl = x_pitl, xi_ptl = xi_ptl, f_ptl = f_ptl, gamma_pil = gamma_pil, 
              epsilon_pitl = epsilon_pitl)
  
  return(res)
}

generate_pitl_wo_covariate_change <- function(N, 
                                              TT, 
                                              N_tr, 
                                              T0, 
                                              D,
                                              k_pl_, 
                                              r_pl_,
                                              beta_pl,
                                              alpha_pil,
                                              Phi_p_xi_l,
                                              Phi_p_f_l,
                                              gamma_pil, 
                                              tau_pitl,
                                              change_rate_delta,
                                              intercept_delta) {
  
  x_pitl <- rnorm(N*TT*k_pl_) |> array(dim = c(N, TT, k_pl_))
  
  xi_ptl <- matrix(0, TT, k_pl_)
  for(t in 2:TT) for(j in 1:k_pl_) xi_ptl[t,j] <-  Phi_p_xi_l[j]*xi_ptl[t-1,j] + rnorm(1)
  
  f_ptl <- matrix(0, TT, r_pl_)
  for (t in 2:TT) for (j in 1:r_pl_) f_ptl[t,j] <- Phi_p_f_l[j]*f_ptl[t-1,j] + rnorm(1)
  
  delta_pitl <- matrix(0, nrow = N, ncol = TT)
  for (i in 1:N_tr) for (t in (T0[i]+1):TT) delta_pitl[i, t] <- intercept_delta + change_rate_delta*(t - T0[i]) + tau_pitl[i, t]  
  
  epsilon_pitl <- matrix(rnorm(N*TT), nrow = N, ncol = TT)
  p_itl <- p0_itl <- p1_itl <- matrix(0, nrow = N, ncol = TT)
  for (i in 1:N) for (t in 1:TT) {
    p0_itl[i,t] <- sum(x_pitl[i,t,]*beta_pl) + sum(x_pitl[i,t,]*alpha_pil[i, ]) + sum(x_pitl[i,t,]*xi_ptl[t,]) + sum(gamma_pil[i,]*f_ptl[t,]) + epsilon_pitl[i,t]
    p1_itl[i,t] <- p0_itl[i,t]   # 
  }
  
  p_itl <- p0_itl*(1-D) + p1_itl*D
  
  res <- list(p0_itl = p0_itl, p1_itl = p1_itl, delta_pitl = delta_pitl, p_itl = p_itl, x_pitl = x_pitl, xi_ptl = xi_ptl, f_ptl = f_ptl)
  
  return(res)
}

generate_yit <- function(N, 
                         TT, 
                         N_tr,
                         T0,
                         D, 
                         p_itl, 
                         k_y, 
                         k_y1,
                         k_y2, 
                         r_y,
                         k_y_phi,
                         beta_y,
                         alpha_yi,
                         Phi_y_xi,
                         Phi_y_f,
                         gamma_yi,
                         tau_yit,
                         phi_y_delta,
                         change_rate_delta,
                         intercept_delta = 0) {
  
  tmp <- rnorm(N*TT*k_y2) |> array(dim = c(N, TT, k_y2))  
  tmp0 <- tmp1 <- rep(0, N*TT*k_y2) |> array(dim = c(N, TT, k_y1))
  
  for(l in 1:k_y1) {
    tmp0[,,l] <- p_itl[[l]]$p0_itl
    tmp1[,,l] <- p_itl[[l]]$p1_itl
  }
  
  x0_yit <- abind(tmp0, tmp, along = 3)
  x1_yit <- abind(tmp1, tmp, along = 3)
  
  x_yit <- rep(0, N*TT*k_y) |> array(dim = c(N, TT, k_y))
  for(l in 1:k_y) x_yit[,,l] <- (1-D)*x0_yit[,,l] + D*x1_yit[,,l]
  
  xi_yt <- matrix(rep(0, TT*k_y), nrow = TT, ncol = k_y)
  for (t in 2:TT) for (j in 1:k_y) xi_yt[t,j] <- Phi_y_xi[j]*xi_yt[t-1, j] + rnorm(1)
  
  f_yt <- matrix(rep(0, TT*r_y), nrow = TT, ncol = r_y)
  for (t in 2:TT) for(j in 1:r_y) f_yt[t,j] <- Phi_y_f[j]*f_yt[t-1,j] + rnorm(1)
  
  X_y_delta <- matrix(rnorm(N*TT*k_y_phi), nrow = N*TT, ncol = k_y_phi)
  delta_yit <- matrix(0, nrow = N, ncol = TT)
  mu <- X_y_delta%*%phi_y_delta |> matrix(nrow = TT, ncol = N) |> t()
  for (i in 1:N_tr) for (t in (T0[i]+1):TT) delta_yit[i, t] <- mu[i,t] + intercept_delta + change_rate_delta*(t - T0[i]) + tau_yit[i, t]  
  
  epsilon_yit <- matrix(rnorm(N*TT), nrow = N, ncol = TT)
  y_it <- y0_it <- y1_it <- matrix(0, nrow = N, ncol = TT)
  for (i in 1:N) for (t in 1:TT) y0_it[i,t] <- sum(x0_yit[i,t,]*beta_y) + sum(x0_yit[i,t,]*alpha_yi[i,]) + sum(x0_yit[i,t,]*xi_yt[t,]) + sum(gamma_yi[i,]*f_yt[t,]) + epsilon_yit[i,t]
  for (i in 1:N) for (t in 1:TT) y1_it[i,t] <- sum(x1_yit[i,t,]*beta_y) + sum(x1_yit[i,t,]*alpha_yi[i,]) + sum(x1_yit[i,t,]*xi_yt[t,]) + sum(gamma_yi[i,]*f_yt[t,]) + delta_yit[i,t] + epsilon_yit[i,t]
  y_it <- y0_it*(1-D) + y1_it*D
  
  
  res <- list(y0_it = y0_it, y1_it = y1_it, delta_yit = delta_yit, 
              y_it = y_it, x0_yit = x0_yit, x1_yit = x1_yit, x_yit = x_yit, xi_yt = xi_yt, f_yt = f_yt, X_y_delta = X_y_delta,
              k_y_phi = k_y_phi)
  return(res)
}

generate_yit_endo_mediator <- function(N, 
                         TT, 
                         N_tr,
                         T0,
                         D, 
                         p_itl, 
                         k_y, 
                         k_y1,
                         k_y2, 
                         r_y,
                         k_y_phi,
                         beta_y,
                         alpha_yi,
                         Phi_y_xi,
                         Phi_y_f,
                         gamma_yi,
                         tau_yit,
                         phi_y_delta,
                         change_rate_delta,
                         intercept_delta = 0) {
  
  tmp <- rnorm(N*TT*k_y2) |> array(dim = c(N, TT, k_y2))  
  tmp0 <- tmp1 <- rep(0, N*TT*k_y2) |> array(dim = c(N, TT, k_y1))
  
  for(l in 1:k_y1) {
    tmp0[,,l] <- p_itl[[l]]$p0_itl
    tmp1[,,l] <- p_itl[[l]]$p1_itl
  }
  
  x0_yit <- abind(tmp0, tmp, along = 3)
  x1_yit <- abind(tmp1, tmp, along = 3)
  
  x_yit <- rep(0, N*TT*k_y) |> array(dim = c(N, TT, k_y))
  for(l in 1:k_y) x_yit[,,l] <- (1-D)*x0_yit[,,l] + D*x1_yit[,,l]
  
  xi_yt <- matrix(rep(0, TT*k_y), nrow = TT, ncol = k_y)
  for (t in 2:TT) for (j in 1:k_y) xi_yt[t,j] <- Phi_y_xi[j]*xi_yt[t-1, j] + rnorm(1)
  
  f_yt <- matrix(rep(0, TT*r_y), nrow = TT, ncol = r_y)
  for (t in 2:TT) for(j in 1:r_y) f_yt[t,j] <- Phi_y_f[j]*f_yt[t-1,j] + rnorm(1)
  
  ## replace the first factor with factor from p_itl[[1]]
  f_yt[,1] <- p_itl[[1]]$f_ptl[,1]
  
  ## update the first column of gamma_yi with p_itl[[1]]$gamma_pil[,1]
  gamma_yi[,1] <- p_itl[[1]]$gamma_pil[,1] + rnorm(50, mean = 0, sd = 0.5)
  
  
  X_y_delta <- matrix(rnorm(N*TT*k_y_phi), nrow = N*TT, ncol = k_y_phi)
  delta_yit <- matrix(0, nrow = N, ncol = TT)
  mu <- X_y_delta%*%phi_y_delta |> matrix(nrow = TT, ncol = N) |> t()
  for (i in 1:N_tr) for (t in (T0[i]+1):TT) delta_yit[i, t] <- mu[i,t] + intercept_delta + change_rate_delta*(t - T0[i]) + tau_yit[i, t]  
  
  epsilon_yit <- matrix(rnorm(N*TT), nrow = N, ncol = TT)
  y_it <- y0_it <- y1_it <- matrix(0, nrow = N, ncol = TT)
  for (i in 1:N) for (t in 1:TT) y0_it[i,t] <- sum(x0_yit[i,t,]*beta_y) + sum(x0_yit[i,t,]*alpha_yi[i,]) + sum(x0_yit[i,t,]*xi_yt[t,]) + sum(gamma_yi[i,]*f_yt[t,]) + epsilon_yit[i,t]
  for (i in 1:N) for (t in 1:TT) y1_it[i,t] <- sum(x1_yit[i,t,]*beta_y) + sum(x1_yit[i,t,]*alpha_yi[i,]) + sum(x1_yit[i,t,]*xi_yt[t,]) + sum(gamma_yi[i,]*f_yt[t,]) + delta_yit[i,t] + epsilon_yit[i,t]
  y_it <- y0_it*(1-D) + y1_it*D
  
  
  res <- list(y0_it = y0_it, y1_it = y1_it, delta_yit = delta_yit, 
              y_it = y_it, x0_yit = x0_yit, x1_yit = x1_yit, x_yit = x_yit, xi_yt = xi_yt, f_yt = f_yt, X_y_delta = X_y_delta,
              k_y_phi = k_y_phi,
              gamma_yi = gamma_yi, epsilon_yit = epsilon_yit)
  return(res)
}

convert2estimableData <- function(N, 
                                 TT, 
                                 T0,
                                 D,
                                 N_tr, 
                                 N_co, 
                                 k_y,
                                 k_y1,
                                 k_y2,
                                 k_y_phi,
                                 k_pl,
                                 p_itl,
                                 y_it, 
                                 beta_y, 
                                 alpha_yi, 
                                 delta_pitl,
                                 treatment_ids) {
  id <- rep(1:N, each = TT)
  time <- rep(1:TT, N)
  Y <- as.vector(t(y_it$y_it))
  D_vec <- as.vector(t(D))
  direct_eff <- as.vector(t(y_it$delta_yit))
  total_eff <- as.vector(t(y_it$y1_it - y_it$y0_it))
  
  mediated_eff <- matrix(0, nrow = N, ncol = TT)
  x0_yit <- y_it$x0_yit
  x1_yit <- y_it$x1_yit
  xi_yt <- y_it$xi_yt
  
  for (i in 1:N) for (t in 1:TT) mediated_eff[i,t] <- sum((x1_yit[i,t,] - x0_yit[i,t,])*beta_y  + (x1_yit[i,t,] - x0_yit[i,t,])*alpha_yi[i,]  + (x1_yit[i,t,] - x0_yit[i,t,])*xi_yt[t,])
  mediated_eff <- as.vector(t(mediated_eff))
  effs <- cbind(mediated_eff, direct_eff, total_eff)
  print(sum(abs(effs[,1] + effs[,2] - effs[,3])))   # this should be approximately zero
  
  x_yit <- y_it$x_yit  # covariates in outcome equation
  
  X <- matrix(rep(0, N*TT*k_y), nrow = N*TT, ncol = k_y)
  for(j in 1:k_y) X[,j] <- as.vector( t(  x_yit[,,j]  )  )
  simdataY <- data.frame(id, time, Y, D_vec, total_eff, direct_eff, mediated_eff, X) |> mutate(treat = c(rep(1, N_tr*TT), rep(0, N_co*TT))) |> rename(D = D_vec)
  
  treated_idx <- which(simdataY$D == 1)
  ctrl_idx <- which(simdataY$D == 0)
  treated_idx_by_unit <- ctrl_idx_by_unit <- list()
  
  for(i in 1:N) {
    tmp <- simdataY |> filter(id == i & D == 1) |> select(time) |> unlist() |> unname()
    treated_idx_by_unit[[i]] <- tmp
    
    tmp <- simdataY |> filter(id == i & D == 0) |> select(time) |> unlist() |> unname()
    ctrl_idx_by_unit[[i]] <- tmp
  }  
  
  Xp <- X[,1:k_y1]
  Xq <- X[,(k_y1 + 1):(k_y)]
  X_y_delta <- y_it$X_y_delta
  
  simdataY <- list(dat = simdataY, Xp = as.matrix(Xp), Xq = as.matrix(Xq), Xdelta = X_y_delta, TT = TT, N = N, N_co = N_co, N_tr = N_tr, 
                   T0 = T0, k_y = k_y, k_y1 = k_y1, k_y2 = k_y2, k_y_phi = k_y_phi,
                   treated_unit_ids = 1:N_tr, control_unit_ids = (N_tr + 1):N, 
                   treated_idx_by_unit = treated_idx_by_unit, ctrl_idx_by_unit = ctrl_idx_by_unit,
                   treated_idx = treated_idx, ctrl_idx = ctrl_idx)
  
  
 simdataP <- vector(mode= "list", length = k_y1)  
  for(l in 1:k_y1) {
    p_eff <- p_itl[[l]]$delta_pitl |> t() |> as.vector()
    Xp_l <- matrix(nrow = N*TT, ncol = k_pl[l])
    
    for(j in 1:k_pl[l]) Xp_l[,j] <- p_itl[[l]]$x_pitl[,,j] |> t() |> as.vector()
    
    p <- p_itl[[l]]$p_itl |> t() |> as.vector()
    simdataP_ <- data.frame(id, time, D_vec, p_eff, p, Xp_l) |> mutate(treat = c(rep(1, N_tr*TT), rep(0, N_co*TT))) |> 
      rename(D = D_vec)
    
    Xp <- data.frame(Xp_l)
    
    dataP_ <- list(dat = simdataP_, Xp = Xp)
    simdataP[[l]] <- dataP_
  }
  
  simdataP[["TT"]] <- TT
  simdataP[["N"]] <- N
  simdataP[["N_co"]] <- N_co
  simdataP[["N_tr"]] <- N_tr
  simdataP[["T0"]] <- T0
  simdataP[["k_y"]] <- k_y
  simdataP[["k_y1"]] <- k_y1
  simdataP[["k_pl"]] <- k_pl
  simdataP[["treated_unit_ids"]] <- 1:N_tr
  simdataP[["control_unit_ids"]] <- (N_tr + 1):N
  simdataP[["treated_idx_by_unit"]] <- treated_idx_by_unit
  simdataP[["ctrl_idx_by_unit"]] <- ctrl_idx_by_unit
  simdataP[["treated_idx"]] <- treated_idx
  simdataP[["ctrl_idx"]] <- ctrl_idx

  simdata <- list(dataY = simdataY, dataP = simdataP)
  
  return(simdata)
}

#--------------------- Functions to check estimation results of simulation data -------------------#
### Only for simulation data 

prep4estimation_of_sim_data <- function(simdata) {
  
  load(simdata)
  
  dataY <- simdata$dataY
  dataP <- simdata$dataP
  N <- dataY$N
  TT <- dataY$TT
  T0 <- dataY$T0  
  T0 <- rep(T0, each = TT)
  time_diff <- rep(1:TT, N) - T0
  
  total_eff <- dataY$dat$total_eff
  mediated_eff <- dataY$dat$mediated_eff
  direct_eff <- dataY$dat$direct_eff
  
  k_y1 <- dataY$k_y1
  
  p_eff <- matrix(nrow = N*TT, ncol = k_y1)
  
  for(l in 1:k_y1) p_eff[,l] <- dataP[[l]]$dat$p_eff    ## treatment effects on the k_y1 endogenous variables.
  colnames(p_eff) <- paste0("p_eff", 1:k_y1)
  
  df_eligible <- dataY$dat
  df_eligible$time_diff <- time_diff
  
  Xdelta <- dataY$Xdelta
  
  colnames(Xdelta) <- paste0("Xdelta", 1:ncol(Xdelta))  
  
  k_pl <- dataP$k_pl
  XP <- matrix(0, nrow = N*TT, ncol = sum(k_pl))
  colnames_XP <- vector(mode = "character")
  for(l in 1:k_y1) {
    if(l == 1) idx <- 1:k_pl[l] else idx <- 1:k_pl[l] + k_pl[-1]
    
    XP[,idx] <- as.matrix(dataP[[l]]$Xp)
    colnames_XP <- c(colnames_XP,     paste0("XP", l, "_", 1:length(idx)))
  }
  
  colnames(XP) <- colnames_XP
  
  df_eligible <- cbind(df_eligible, Xdelta, XP, p_eff)  # df_eligible is the ultimate data frame that will be used in estimation.
  
  return(df_eligible)
}

checkMCMC_MediatorEq <- function(dataP, MCMC_P, display_effects_only, true_param_RData) {
  
  k_y1 <- dataP$k_y1
  N_tr <- dataP$N_tr
  load(true_param_RData)
  
  message("There are ", k_y1, " Mediator Equations.")

  
  for(l in 1:k_y1) {
    readline(paste0("Press Enter to check Mediator Equation ", l))
  
  MCMC_p_beta <- MCMC_P$beta[[l]]
  MCMC_p_mu_alpha <- MCMC_P$mu_alpha[[l]]
  MCMC_p_xi <- MCMC_P$xi[[l]]
  MCMC_p_f <- MCMC_P$f[[l]]
  MCMC_p_phi_xi <- MCMC_P$phi_xi[[l]]
  MCMC_p_phi_f <- MCMC_P$phi_f[[l]]
  MCMC_p_sigma2_e <- MCMC_P$sigma2_e[[l]]
  MCMC_p_sigma2_eps <- MCMC_P$sigma2_eps[[l]]
  MCMC_p_pi <- MCMC_P$pi[[l]]
  MCMC_p_theta <- MCMC_P$theta[[l]]
  MCMC_p_tau2 <- MCMC_P$tau2[[l]]
  MCMC_p_s <- MCMC_P$s[[l]]
  MCMC_p_delta <- MCMC_P$delta[[l]]
  MCMC_p_phi_delta <- MCMC_P$phi_delta[[l]] 
  MCMC_p_sigma2_eta <- MCMC_P$sigma2_eta[[l]]
  
  if(display_effects_only == 0)
  {
    cat("Displaying parameter estimates and treatment effects\n")
  } else {
    cat("Displaying treatment effects only\n")
  }
  if(display_effects_only == 0) {
    r_pl <- dim(MCMC_p_f)[2]
      
    par(mfrow = c(2,2))
    matplot(MCMC_p_beta, type = "l")
    matplot(MCMC_p_mu_alpha, type = "l")
    
    kk <- MCMC_p_beta + MCMC_p_mu_alpha
    matplot(kk, type = "l")
    
    kk[,1] <- kk[,1] + mean(MCMC_p_xi[,1,])
    kk[,2] <- kk[,2] + mean(MCMC_p_xi[,2,])
    kk[,3] <- kk[,3] + mean(MCMC_p_xi[,3,])
    matplot(kk, type = "l")
  
    par(mfrow = c(1,1))
    
    xi1 <- rowMeans(MCMC_p_xi[,1,])
    xi2 <- rowMeans(MCMC_p_xi[,2,])
    xi3 <- rowMeans(MCMC_p_xi[,3,])
    xi <- cbind(xi1, xi2, xi3)
    
    xi_ptl <- true_paramp0[[l]]$xi_t
    par(mfrow = c(2,3))
    matplot(cbind(xi_ptl[,1], xi1), type = "l")
    matplot(cbind(xi_ptl[,2], xi2), type = "l")
    matplot(cbind(xi_ptl[,3], xi3), type = "l")
    plot(xi_ptl[,1], xi1)
    plot(xi_ptl[,2], xi2)
    plot(xi_ptl[,3], xi3)
    
    if(r_pl > 0) {
      f1 <- t(MCMC_p_f[,1,])
      f2 <- t(MCMC_p_f[,2,])
      f3 <- t(MCMC_p_f[,3,])
      f1 <- colMeans(f1)
      f2 <- colMeans(f2)
      f3 <- colMeans(f3)
    
     f_ptl <- true_paramp0[[l]]$f_p_t
      par(mfrow = c(2,3))
      plot(f1, type = "l")
      plot(f2, type = "l")
      plot(f3, type = "l")
      plot(f_ptl[,1], type = "l")
      plot(f_ptl[,2], type = "l")
      
      par(mfrow = c(2,3))
      plot(f_ptl[,1], f1)
      plot(f_ptl[,1], f2)
      plot(f_ptl[,1], f3)
      plot(f_ptl[,2], f1)
      plot(f_ptl[,2], f2)
      plot(f_ptl[,2], f3)
    }
    
    par(mfrow = c(1,3))
    apply(MCMC_p_phi_xi, 2, hist, main = "phi_xi")
    if(r_pl > 0) apply(MCMC_p_phi_f, 2, hist, main = "phi_f")
    apply(MCMC_p_sigma2_e, 2, hist, main = "sigma2_e")
    
    par(mfrow = c(1,1))
    hist(MCMC_p_sigma2_eps, main = "sigma2_eps")
    
    if(r_pl > 0) {
      par(mfrow = c(3,2))
      plot(MCMC_p_pi[,1], main = "pi1"); hist(MCMC_p_pi[,1], main = "pi1")
      plot(MCMC_p_pi[,2], main = "pi2"); hist(MCMC_p_pi[,2], main = "pi2")
      plot(MCMC_p_pi[,3], main = "pi3"); hist(MCMC_p_pi[,3], main = "pi3")
      
      plot(MCMC_p_theta, type = "l", main = "theta"); hist(MCMC_p_theta, main = "theta")
      plot(MCMC_p_tau2, type = "l", main = "tau2"); hist(MCMC_p_tau2, main = "tau2")
      plot(MCMC_p_s, type = "l", main = "s"); hist(MCMC_p_s, main = "s")
    }
  }
  
  p_delta_avg <- colMeans(MCMC_p_delta) 
  par(mfrow = c(1,1))
  compare <- cbind(dataP[[l]]$dat$p_eff, p_delta_avg) |> data.frame() |> cbind(dataP[[l]]$dat$D)
  colnames(compare)[ncol(compare)] <- "D"
  compare <- compare |> filter(D != 0) |> select(-D)
  cat("Correlation between Actual and Predicted Treatment Effect on Mediator: ", cor(compare)[1,2])
  
  tt <- t(apply(MCMC_p_delta, 2, hdi, credMass = 0.95)) %>% data.frame()
  p_delta_median <- apply(MCMC_p_delta, 2, median) 
  tt <- cbind(tt, p_delta_median, p_delta_avg)
  
  tmp <- dataP[[l]]$dat |> select(id, time, D, p, p_eff) |> 
    mutate(T0 = 25, time_diff = time - T0) |> cbind(tt) |> filter(id <= N_tr)
  
  p <- ggplot(tmp) + geom_line(aes(x = time_diff, y = p_eff), col = "red", linetype = "dashed", size = 1) + 
    geom_line(aes(x = time_diff, y = p_delta_median), col = "black", size = 1) + 
    geom_ribbon(aes(x = time_diff, ymin = lower, ymax = upper), alpha=0.25)  + theme_bw() + 
    xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
    ggtitle("Treatment Effect on Mediator")  + facet_wrap(~id)
  
  print(p)
  }
}
checkMCMC_OutcomeEq <- function(dataY, MCMC_Y, display_effects_only, true_param_RData) {
  
  k_y <- dataY$k_y - 1
  N_tr <- dataY$N_tr
  TT <- dataY$TT
  r_y <- dim(MCMC_Y$f)[2]
  T0 <- dataY$T0
  
  MCMC_y_beta <- MCMC_Y$beta
  MCMC_y_alpha_i <- MCMC_Y$alpha_i
  MCMC_y_mu_alpha <- MCMC_Y$mu_alpha
  MCMC_y_xi <- MCMC_Y$xi
  MCMC_y_f <- MCMC_Y$f
  MCMC_y_phi_xi <- MCMC_Y$phi_xi
  MCMC_y_phi_f <- MCMC_Y$phi_f
  MCMC_y_sigma2_e <- MCMC_Y$sigma2_e
  MCMC_y_sigma2_eps <- MCMC_Y$sigma2_eps
  MCMC_y_pi <- MCMC_Y$pi
  MCMC_y_theta <- MCMC_Y$theta
  MCMC_y_tau2 <- MCMC_Y$tau2
  MCMC_y_s <- MCMC_Y$s
  MCMC_y_delta <- MCMC_Y$delta
  MCMC_y_tte <- MCMC_Y$tte
  MCMC_y_phi_delta <- MCMC_Y$phi_delta
  MCMC_y_mte<- MCMC_Y$mte
  
  load(true_param_RData)
  
  if(display_effects_only == 0) {
    cat("Displaying parameter estimates and treatment effects\n")
  } else {
    cat("Displaying treatment effects only\n")
  }
  
  if(display_effects_only == 0) {
    par(mfrow = c(1,1))
    kk <- MCMC_y_beta + MCMC_y_mu_alpha
    for(j in 1:k_y) kk[,j] <- kk[,j] + mean(MCMC_y_xi[,j,])
    matplot(kk, type = "l")
    
    xi_yt <- true_paramy0$xi_t
    xi <- matrix(nrow = TT, ncol = k_y)
    for(j in 1:k_y) xi[,j] <- rowMeans(MCMC_y_xi[,j,]) - mean(MCMC_y_xi[,j,])
    
    ncols <- 3
    nrows <- ceiling(k_y/ncols)
    par(mfrow = c(nrows,ncols))
    for(j in 1:k_y) matplot(cbind(xi[,j], xi_yt[,j]), type = "l", xlab = "Time", ylab = "")
    
    for(j in 1:k_y) plot(xi_yt[,j], xi[,j])
  
    f_y_t <- true_paramy0$f_t
    true_no_factors <- ncol(f_y_t)
    
    if(r_y > 0) {
      par(mfrow = c(true_no_factors, r_y))  
      f_yt <- matrix(nrow = TT, ncol = r_y)
      for(j in 1:r_y) f_yt[,j] <- t(MCMC_y_f[,j,]) |> colMeans()
      apply(f_yt, 2, plot, type = "l")
      apply(f_y_t, 2, plot, type = "l")
      
      par(mfrow = c(true_no_factors, r_y))  
      for(i in 1:true_no_factors) for(j in 1:r_y)  plot(f_y_t[,i], f_yt[,j])
    }
  
    ncols <- 3
    nrows <- ceiling(k_y/ncols)
    par(mfrow = c(nrows,ncols))
    apply(MCMC_y_phi_xi, 2, hist, main = "phi_xi")
    apply(MCMC_y_sigma2_e, 2, hist, main = "sigma2_e")
    
    if(r_y > 0) {
      ncols <- 3
      nrows <- ceiling(r_y/ncols)
      par(mfrow = c(nrows,ncols))
      apply(MCMC_y_phi_f, 2, hist, main = "phi_f")
    }
    
    par(mfrow = c(1,1))
    hist(MCMC_y_sigma2_eps, main = "sigma2_eps")
    
    if (r_y > 0) {
      par(mfrow = c(r_y,2))
      
      for(j in 1:r_y) {
        plot(MCMC_y_pi[,j], main = paste0("pi", j))
        hist(MCMC_y_pi[,j], main = paste0("pi", j), xlim = c(0, 1), breaks = seq(0, 1, by = 0.01), xlab = "", ylab = "Density", freq = FALSE)
      }
      par(mfrow = c(3,2))
      plot(MCMC_y_theta, type = "l", main = "theta"); hist(MCMC_y_theta, main = "theta")
      plot(MCMC_y_tau2, type = "l", main = "tau2"); hist(MCMC_y_tau2, main = "tau2")
      plot(MCMC_y_s, type = "l", main = "s"); hist(MCMC_y_s, main = "s")
    
    }
    
    
    ncols <- ncol(MCMC_y_phi_delta)
    nrows <- ceiling(ncols/3)
    par(mfrow=c(nrows,3))
    apply(MCMC_y_phi_delta, 2, hist)
  }

  y_tte_avg <- colMeans(MCMC_y_tte)
  par(mfrow = c(1,1))
  compare <- cbind(dataY$dat$total_eff, y_tte_avg) |> data.frame() |> cbind(dataY$dat$D) |> filter(`dataY$dat$D` != 0) |> select(-`dataY$dat$D`)
  cat("Correlation between Actual and Predicted Total Treatment Effect: ", cor(compare)[1,2], "\n")
  
  tt <- t(apply(MCMC_y_tte, 2, hdi, credMass = 0.95)) %>% data.frame() 
  y_tte_median <- apply(MCMC_y_tte, 2, median) 
  tt <- cbind(tt, y_tte_median, y_tte_avg)
  
  T0_ <- rep(T0, each = TT)
  tmp <- dataY$dat |> select(id, time, D, Y, total_eff, mediated_eff, direct_eff) |> 
    mutate(T0 = T0_, time_diff = time - T0_) |> cbind(tt)
  
  tmp2 <- tmp |> filter(id <= N_tr)
  p <- ggplot(tmp2) + geom_line(aes(x = time_diff, y = total_eff), col = "red", linetype = "dashed", size = 1) + 
    geom_line(aes(x = time_diff, y = y_tte_median), col = "black", size = 1) + 
    geom_ribbon(aes(x = time_diff, ymin = lower, ymax = upper), alpha=0.25) +
    xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + theme_bw() +
    ggtitle("Total Treatment Effect: Actual (Red Dashed) vs. Estimated (Black Solid) with 95% HDI (Grey)")  + 
    facet_wrap(~id)
  
  print(p)
  
  y_mte_avg <- colMeans(MCMC_y_mte)
  par(mfrow = c(1,1))
  compare <- cbind(dataY$dat$mediated_eff, y_mte_avg) |> data.frame() |> cbind(dataY$dat$D) |> filter(`dataY$dat$D` != 0) |> select(-`dataY$dat$D`)
  cat("Correlation between Actual and Predicted Mediated Effect: ", cor(compare)[1,2], "\n")
  
  tt <- t(apply(MCMC_y_mte, 2, hdi, credMass = 0.95)) %>% data.frame() 
  y_mte_avg <- colMeans(MCMC_y_mte)
  y_mte_median <- apply(MCMC_y_mte, 2, median) 
  
  tt <- cbind(tt, y_mte_median, y_mte_avg)
  
  T0_ <- rep(T0, each = TT)
  tmp <- dataY$dat |> select(id, time, D, Y, total_eff, mediated_eff, direct_eff) |> 
    mutate(T0 = T0_, time_diff = time - T0_) |> cbind(tt)
  
  tmp2 <- tmp |> filter(id <= N_tr)
  p <- ggplot(tmp2) + geom_line(aes(x = time_diff, y = mediated_eff), col = "red", linetype = "dashed", size = 1) + 
    geom_line(aes(x = time_diff, y = y_mte_median), col = "black", size = 1) + 
    geom_ribbon(aes(x = time_diff, ymin = lower, ymax = upper), alpha=0.25) +
    xlab("") + ylab("")  + geom_vline(xintercept = 0, color = "grey", size = 1)  + theme_bw() + 
    ggtitle("Mediated Effects: Actual (Red Dashed) vs. Estiamted (Black Solid) with 95% HDI (Grey)")  + 
    facet_wrap(~id)
  
  print(p)
  
  y_de_avg <- colMeans(MCMC_y_delta)
  par(mfrow = c(1,1))
  compare <- cbind(dataY$dat$direct_eff, y_de_avg) |> data.frame() |> cbind(dataY$dat$D) |> filter(`dataY$dat$D` != 0) |> select(-`dataY$dat$D`)
  cat("Correlation between Actual and Predicted Direct Effect: ", cor(compare)[1,2], "\n")
  
  tt <- t(apply(MCMC_y_delta, 2, hdi, credMass = 0.95)) %>% data.frame() 
  y_delta_avg <- colMeans(MCMC_y_delta)
  y_delta_median <- apply(MCMC_y_delta, 2, median) 
  
  tt <- cbind(tt, y_delta_median, y_delta_avg)

  T0_ <- rep(T0, each = TT)
  tmp <- dataY$dat |> select(id, time, D, Y, total_eff, mediated_eff, direct_eff) |> 
    mutate(T0 = T0_, time_diff = time - T0_) |> cbind(tt)
  
  tmp2 <- tmp |> filter(id <= N_tr)
  p <- ggplot(tmp2)  + geom_vline(xintercept = 0, color = "grey", size = 1)  + theme_bw() + 
    geom_line(aes(x = time_diff, y = direct_eff), col = "red", linetype = "dashed", size = 1) + 
    geom_line(aes(x = time_diff, y = y_delta_median), col = "black", size = 1) + 
    geom_ribbon(aes(x = time_diff, ymin = lower, ymax = upper), alpha=0.25) +
    xlab("") + ylab("") +
    ggtitle("Direct Effect: Actual (Red Dashed) vs. Estiamted (Black Solid) with 95% HDI (Grey)")  + 
    facet_wrap(~id)
  
  print(p)
  
}
post_estimation_checking_sim_data <- function(res, simdata, true_param_RData, display_effects_only = 1) {
  load(simdata)
  dataY <- simdata$dataY
  dataP <- simdata$dataP
  MCMC_P <- res$MCMC_P
  MCMC_Y <- res$MCMC_Y
  
  checkMCMC_MediatorEq(dataP, MCMC_P, display_effects_only, true_param_RData = true_param_RData)
  checkMCMC_OutcomeEq(dataY, MCMC_Y, display_effects_only, true_param_RData = true_param_RData)
}

#--------------------- Summary functions MCMC Results -------------------#
summarize_MCMC_MediatorEq <- function(dataP, MCMC_P, display_effects_individually = 0, display_effects_only = 1) {
  
  k_y1 <- length(dataP)
  k_pl <- vector(mode = "numeric", length = k_y1)
  
  message("There are ", k_y1, " Mediator Equation(s).")
  
  for(l in 1:k_y1) k_pl[l] <- ncol(dataP[[l]]$Xp)
  
  for (l in 1:k_y1) {
    readline(paste0("Press Enter to visualize the treatment's effects on Mediator ", l))
    
    TT <- dataP[[l]]$TT
    N_tr <- dataP[[l]]$N_tr
  
    MCMC_p_beta <- MCMC_P$beta[[l]] 
    MCMC_p_alpha_i <- MCMC_P$alpha_i[[l]] 
    MCMC_p_xi <- MCMC_P$xi[[l]] 
    MCMC_p_f <- MCMC_P$f[[l]] 
    MCMC_p_gamma_i <- MCMC_P$gamma_i[[l]] 
    MCMC_p_phi_xi <- MCMC_P$phi_xi[[l]]
    MCMC_p_phi_f <- MCMC_P$phi_f[[l]] 
    MCMC_p_sigma2_e <- MCMC_P$sigma2_e[[l]] 
    MCMC_p_sigma2_eps <- MCMC_P$sigma2_eps[[l]] 
    MCMC_p_pi <- MCMC_P$pi[[l]] 
    MCMC_p_theta <- MCMC_P$theta[[l]] 
    MCMC_p_tau2 <- MCMC_P$tau2[[l]] 
    MCMC_p_s <- MCMC_P$s[[l]] 
    MCMC_p_mu_alpha <- MCMC_P$mu_alpha[[l]] 
    MCMC_p_p0_mis <- MCMC_P$p0_mis[[l]] 
    MCMC_p_delta <- MCMC_P$delta[[l]]
    MCMC_p_phi_delta <- MCMC_P$phi_delta[[l]] 
    MCMC_p_sigma2_eta <- MCMC_P$sigma2_eta[[l]]
    
    r_pl <- dim(MCMC_p_f)[2]
    
    if(display_effects_only == 0) {
      
      par(mfrow = c(1,1))
      kk <- MCMC_p_beta + MCMC_p_mu_alpha
      for(j in 1:k_pl[l]) kk[,j] <- kk[,j] + mean(MCMC_p_xi[,j,])
      matplot(kk, type = "l", main = "Traceplot of Coefficients")
      
      ncols <- 3
      nrows <- ceiling(k_pl[l]/ncols)
      par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0))
      apply(kk, 2, hist, main = "", xlab = "", ylab = "")
      mtext("Coefficients", outer = TRUE, cex = 1.5)
      
      xi <- matrix(nrow = TT, ncol = k_pl[l])
      for(j in 1:k_pl[l]) xi[,j] <- rowMeans(MCMC_p_xi[,j,]) - mean(MCMC_p_xi[,j,])
      
      ncols <- 3
      nrows <- ceiling(k_pl[l]/ncols)
      par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0))
      apply(xi, 2, plot, type = "l", xlab = "time", ylab = "xi")
      mtext("Time-Varying Coefficients", outer = TRUE, cex = 1.5)
      
      if(r_pl > 0 & r_pl <= 30) {
        ncols <- 3
        nrows <- ceiling(r_pl/ncols)
        par(mfrow = c(nrows,ncols), mar = c(2,2,2,2))
        f_pt <- matrix(nrow = TT, ncol = r_pl)
        for(j in 1:r_pl) f_pt[,j] <- t(MCMC_p_f[,j,]) |> colMeans()
        apply(f_pt, 2, plot, type = "l")
        mtext("Latent Factors", outer = TRUE, cex = 1.5)
      }
      
      ncols <- 3
      nrows <- ceiling(k_pl[l]/ncols)
      par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0))
      apply(MCMC_p_phi_xi, 2, hist, main = "phi_xi")
      apply(MCMC_p_sigma2_e, 2, hist, main = "", xlab = "")
      mtext("sigma2_e", outer = TRUE, cex = 1.5)
      
      if (r_pl > 0 & r_pl <= 30) {
        ncols <- 3
        nrows <- ceiling(r_pl/ncols)
        par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0), mar = c(2,2,2,2))
        apply(MCMC_p_phi_f, 2, hist, main = "phi_f")
        mtext("Phi f", outer = TRUE, cex = 1.5)
      }
      
      par(mfrow = c(1,1))
      hist(MCMC_p_sigma2_eps, main = "sigma2_epsilon")
      
      if(r_pl > 0 & r_pl <= 30 & MCMC_P$factor_selection_method[l] == "spike-slab") {
        par(mfrow = c(5,2), oma = c(0,0,2,0), mar = c(2,2,2,2))
        for(j in 1:r_pl) {
          plot(MCMC_p_pi[,j], type = "l", main = paste0("pi", j))
          hist(MCMC_p_pi[,j], main = paste0("pi", j))
        }
        mtext("Traceplot and histogram of pi's", outer = TRUE, cex = 1.5)
      
        par(mfrow = c(3,2), oma = c(0,0,2,0), mar = c(2,2,2,2))
        plot(MCMC_p_theta, type = "l", main = "theta"); hist(MCMC_p_theta, main = "theta")
        plot(MCMC_p_tau2, type = "l", main = "tau2"); hist(MCMC_p_tau2, main = "tau2")
        plot(MCMC_p_s, type = "l", main = "s"); hist(MCMC_p_s, main = "s")
      }
    }  

    p_delta_avg <- colMeans(MCMC_p_delta)
    p_delta_median <- apply(MCMC_p_delta, 2, median) 
    p_delta <- t(apply(MCMC_p_delta, 2, hdi, credMass = 0.95)) %>% data.frame() %>% rename(p_delta_lb = lower, p_delta_ub = upper)
    p_delta <- cbind(p_delta_avg, p_delta_median, p_delta)
    T0_ <- rep(dataP[[l]]$T0, each = TT)
    tmp <- dataP[[l]]$dat |> select(id, time, D, p) |> mutate(T0 = T0_, time_diff = time - T0_)
    
    p_effects <- cbind(tmp, p_delta)
    
    tmp2 <- p_effects |> filter(id <= N_tr)
    treated_unit_ids_original <- dataP[[l]]$treated_unit_ids_original
    treated_unit_ids <- dataP[[l]]$treated_unit_ids
    id_mapping <- data.frame(treated_unit_ids, treated_unit_ids_original)
    tmp2 <- tmp2 |> left_join(id_mapping, by =c ("id" = "treated_unit_ids"))
    
    if(MCMC_P$factor_selection_method[l] == "horseshoe") variable_selection <- "Horseshoe Prior " else variable_selection <- "Spike-Slab Prior "

    p <- ggplot(tmp2) + 
      geom_line(aes(x = time_diff, y = p_delta_median), col = "black", size = 1) + 
      geom_ribbon(aes(x = time_diff, ymin = p_delta_lb, ymax = p_delta_ub), alpha=0.25) + theme_bw() + 
      xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
      geom_hline(yintercept = 0, color = "red", size = 1) + 
      ggtitle(paste0("Effect of Treatment on Mediator Estimated by BCEndo with ", variable_selection, "(", r_pl, " Factors)")) + facet_wrap(~treated_unit_ids_original)
    
    print(p)
    
    if (display_effects_individually == 1) {
      for(i in 1:N_tr) {
        tmp2_ <- tmp2 |> filter(id == i)
          p <- ggplot(tmp2_) + 
          geom_line(aes(x = time_diff, y = p_delta_median), col = "black", size = 1) + 
          geom_ribbon(aes(x = time_diff, ymin = p_delta_lb, ymax = p_delta_ub), alpha=0.25) + theme_bw() + 
          xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
          geom_hline(yintercept = 0, color = "red", size = 1) + 
          ggtitle(paste0("Effect of Treatment on Mediator Estimated by BCEndo with ", variable_selection, "(", r_pl, " Factors)")) + facet_wrap(~treated_unit_ids_original)
        
        print(p)
      }

    }
    
  }
}
summarize_MCMC_OutcomeEq <- function(dataY, MCMC_Y, display_effects_individually = 0, display_effects_only = 1) {
  MCMC_y_beta <- MCMC_Y$beta 
  MCMC_y_alpha_i <- MCMC_Y$alpha_i 
  MCMC_y_xi <- MCMC_Y$xi 
  MCMC_y_f <- MCMC_Y$f 
  MCMC_y_gamma_i <- MCMC_Y$gamma_i 
  MCMC_y_phi_xi <- MCMC_Y$phi_xi 
  MCMC_y_phi_f <- MCMC_Y$phi_f 
  MCMC_y_sigma2_e <- MCMC_Y$sigma2_e 
  MCMC_y_sigma2_eps <- MCMC_Y$sigma2_eps 
  MCMC_y_pi <- MCMC_Y$pi 
  MCMC_y_theta <- MCMC_Y$theta 
  MCMC_y_tau2 <- MCMC_Y$tau2 
  MCMC_y_s <- MCMC_Y$s 
  MCMC_y_mu_alpha <- MCMC_Y$mu_alpha 
  MCMC_y_y0_mis <- MCMC_Y$y0_mis 
  MCMC_y_tte <- MCMC_Y$tte 
  MCMC_y_delta <- MCMC_Y$delta 
  MCMC_y_mte<- MCMC_Y$mte
  MCMC_y_phi_delta <- MCMC_Y$phi_delta 
  MCMC_y_sigma2_eta <- MCMC_Y$sigma2_eta
  
  k_y <- dataY$k_y
  r_y <- dim(MCMC_y_f)[2]
  TT <- dataY$TT
  N_tr <- dataY$N_tr
  
  # if(var(res$MCMC_Y$MCMC_y_mte[,1]) == 0) # no mediator case
  
  if(display_effects_only == 0) {
    
    par(mfrow = c(1,1))
    kk <- MCMC_y_beta + MCMC_y_mu_alpha
    for(j in 1:k_y) kk[,j] <- kk[,j] + mean(MCMC_y_xi[,j,])
    matplot(kk, type = "l", main = "Traceplot of Coefficients")
    
    ncols <- 3
    nrows <- ceiling(k_y/ncols)
    par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0))
    apply(kk, 2, hist, main = "", xlab = "", ylab = "")
    mtext("Coefficients", outer = TRUE, cex = 1.5)
    xi <- matrix(nrow = TT, ncol = k_y)
    for(j in 1:k_y) xi[,j] <- rowMeans(MCMC_y_xi[,j,]) - mean(MCMC_y_xi[,j,])
    
    ncols <- 3
    nrows <- ceiling(k_y/ncols)
    par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0))
    apply(xi, 2, plot, type = "l", xlab = "time", ylab = "xi")
    mtext("Time-Varying Coefficients", outer = TRUE, cex = 1.5)
    
    if(r_y > 0 & r_y <= 30) {
      ncols <- 3
      nrows <- ceiling(r_y/ncols)
      par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0), mar = c(2,2,2,2))
      f_yt <- matrix(nrow = TT, ncol = r_y)
      for(j in 1:r_y) f_yt[,j] <- t(MCMC_y_f[,j,]) |> colMeans()
      apply(f_yt, 2, plot, type = "l")
      mtext("Latent Factors", outer = TRUE, cex = 1.5)
    }
  
    ncols <- 3
    nrows <- ceiling(k_y/ncols)
    par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0))
    apply(MCMC_y_phi_xi, 2, hist, main = "phi_xi")
    apply(MCMC_y_sigma2_e, 2, hist, main = "", xlab = "")
    mtext("sigma2_e", outer = TRUE, cex = 1.5)
    
    if(r_y > 0 & r_y <= 30) {
      ncols <- 3
      nrows <- ceiling(r_y/ncols)
      par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0), mar = c(2,2,2,2))
      apply(MCMC_y_phi_f, 2, hist, main = "phi_f")
      mtext("Phi f", outer = TRUE, cex = 1.5)
    }
  
    par(mfrow = c(1,1))
    hist(MCMC_y_sigma2_eps, main = "sigma2_epsilon")
    
    if(r_y > 0  & r_y <= 30 & MCMC_Y$factor_selection_method == "spike_slab") {
      par(mfrow = c(5,2), oma = c(0,0,2,0), mar = c(2,2,2,2))
      
      for(j in 1:r_y) {
        plot(MCMC_y_pi[,j], type = "l", main = paste0("pi", j))
        hist(MCMC_y_pi[,j], main = paste0("pi", j))
      }
      
      mtext("Traceplot and histogram of pi's", outer = TRUE, cex = 1.5)
      par(mfrow = c(3,2), oma = c(0,0,2,0), mar = c(2,2,2,2))
      plot(MCMC_y_theta, type = "l", main = "theta"); hist(MCMC_y_theta, main = "theta")
      plot(MCMC_y_tau2, type = "l", main = "tau2"); hist(MCMC_y_tau2, main = "tau2")
      plot(MCMC_y_s, type = "l", main = "s"); hist(MCMC_y_s, main = "s")
    }
    
    ncols <- 3
    nrows <- ceiling(ncol(MCMC_y_phi_delta)/ncols)
    par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0))
    apply(MCMC_y_phi_delta, 2, hist, main = "", xlab = "")
    mtext("Effects of Moderators on Delta", outer = TRUE, cex = 1.5)
  }
  
  y_tte_avg <- colMeans(MCMC_y_tte)
  y_tte_median <- apply(MCMC_y_tte, 2, median) 
  tte <- t(apply(MCMC_y_tte, 2, hdi, credMass = 0.95)) %>% data.frame() %>% rename(y_tte_lb = lower, y_tte_ub = upper)
  tte <- cbind(y_tte_avg, y_tte_median, tte)
  T0_ <- rep(dataY$T0, each = TT)
  tmp <- dataY$dat |> select(id, time, D, Y) |> mutate(T0 = T0_, time_diff = time - T0_) |> cbind(tte)
  
  y_delta_avg <- colMeans(MCMC_y_delta)
  y_delta_median <- apply(MCMC_y_delta, 2, median) 
  y_delta <- t(apply(MCMC_y_delta, 2, hdi, credMass = 0.95)) %>% data.frame() %>% rename(y_delta_lb = lower, y_delta_ub = upper)
  y_delta <- cbind(y_delta_avg, y_delta_median, y_delta)
  
  y_mte_avg <- colMeans(MCMC_y_mte)
  y_mte_median <- apply(MCMC_y_mte, 2, median) 
  y_mte <- t(apply(MCMC_y_mte, 2, hdi, credMass = 0.95)) %>% data.frame() %>% rename(y_mte_lb = lower, y_mte_ub = upper)
  y_mte <- cbind(y_mte_avg, y_mte_median, y_mte)
  
  y_effects <- cbind(tmp, y_delta, y_mte)
  ncols <- 3
  nrows <- ceiling(dataY$N_tr/ncols)
  par(mfrow = c(nrows,ncols), oma  = c(0,0,2,0))
  
  tmp2 <- y_effects |> filter(id <= N_tr)
  
  treated_unit_ids_original <- dataY$treated_unit_ids_original
  treated_unit_ids <- dataY$treated_unit_ids
  id_mapping <- data.frame(treated_unit_ids, treated_unit_ids_original)
  tmp2 <- tmp2 |> left_join(id_mapping, by =c ("id" = "treated_unit_ids"))
  
  if(MCMC_Y$factor_selection_method == "horseshoe") variable_selection <- "Horseshoe Prior " else variable_selection <- "Spike-Slab Prior "
  
  p <- ggplot(tmp2) + 
    geom_line(aes(x = time_diff, y = y_tte_avg), col = "black", size = 1) + 
    geom_ribbon(aes(x = time_diff, ymin = y_tte_lb, ymax = y_tte_ub), alpha=0.25)  + theme_bw() + 
    xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
    geom_hline(yintercept = 0, color = "red", size = 1) + 
    ggtitle(paste0("Total Effect of Treatment Estimated by BCEndo with ", variable_selection, "(", r_y, " Factors)")) + facet_wrap(~treated_unit_ids_original)
  
  readline(paste0("Press Enter to visualize the total treatment effect on the outcome"))
  print(p)
  
  if (display_effects_individually == 1) {
    for(i in 1:N_tr) {
      tmp2_ <- tmp2 |> filter(id == treated_unit_ids[i])
      p <- ggplot(tmp2_) + 
        geom_line(aes(x = time_diff, y = y_tte_avg), col = "black", size = 1) + 
        geom_ribbon(aes(x = time_diff, ymin = y_tte_lb, ymax = y_tte_ub), alpha=0.25)  + theme_bw() + 
        xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
        geom_hline(yintercept = 0, color = "red", size = 1) + 
        ggtitle(paste0("Total Effect of Treatment Estimated by BCEndo with ", variable_selection, "(", r_y, " Factors)")) + facet_wrap(~treated_unit_ids_original)
      
      print(p)
    }
  }
  
  if(var(res$MCMC_Y$mte[,1]) > 0) {
    p <- ggplot(tmp2) + 
      geom_line(aes(x = time_diff, y = y_mte_avg), col = "black", size = 1) + 
      geom_ribbon(aes(x = time_diff, ymin = y_mte_lb, ymax = y_mte_ub), alpha=0.25)  + theme_bw() +
      xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
      geom_hline(yintercept = 0, color = "red", size = 1) + 
      ggtitle(paste0("Mediated Effect Estimated by BCEndo with ", variable_selection, "(", r_y, " Factors)")) + facet_wrap(~treated_unit_ids_original)
    
    readline(paste0("Press Enter to visualize the mediated treatment effect on the outcome"))
    print(p)
    
    if(display_effects_individually == 1) {
      for(i in 1:N_tr) {
        tmp2_ <- tmp2 |> filter(id == treated_unit_ids[i])
        p <- ggplot(tmp2_) + 
          geom_line(aes(x = time_diff, y = y_mte_avg), col = "black", size = 1) + 
          geom_ribbon(aes(x = time_diff, ymin = y_mte_lb, ymax = y_mte_ub), alpha=0.25)  + theme_bw() +
          xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
          geom_hline(yintercept = 0, color = "red", size = 1) + 
          ggtitle(paste0("Mediated Effect Estimated by BCEndo with ", variable_selection, "(", r_y, " Factors)")) + facet_wrap(~treated_unit_ids_original)
        
        print(p)
      }
    }
    
    p <- ggplot(tmp2) + 
      geom_line(aes(x = time_diff, y = y_delta_avg), col = "black", size = 1) + 
      geom_ribbon(aes(x = time_diff, ymin = y_delta_lb, ymax = y_delta_ub), alpha=0.25)  + theme_bw() + 
      xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
      geom_hline(yintercept = 0, color = "red", size = 1) + 
      ggtitle(paste0("Direct Effect of Treatment Estimated by BCEndo with ", variable_selection, "(", r_y, " Factors)")) + facet_wrap(~treated_unit_ids_original)
    
    readline(paste0("Press Enter to visualize the direct treatment effect on the outcome"))
    print(p)
    
    if(display_effects_individually == 1) {
      for(i in 1:N_tr) {
        tmp2_ <- tmp2 |> filter(id == treated_unit_ids[i])
        p <- ggplot(tmp2_) + 
          geom_line(aes(x = time_diff, y = y_delta_avg), col = "black", size = 1) + 
          geom_ribbon(aes(x = time_diff, ymin = y_delta_lb, ymax = y_delta_ub), alpha=0.25)  + theme_bw() + 
          xlab("") + ylab("") + geom_vline(xintercept = 0, color = "grey", size = 1) + 
          geom_hline(yintercept = 0, color = "red", size = 1) + 
          ggtitle(paste0("Direct Effect of Treatment Estimated by BCEndo with ", variable_selection, "(", r_y, " Factors)")) + facet_wrap(~treated_unit_ids_original)
        
        print(p)
      }
    }
  }
   
}

plot_treatment_effects <- function(res) {
  
  if ("MCMC_P" %in% names(res)) summarize_MCMC_MediatorEq(res$dataP, res$MCMC_P, display_effects_individually = 0, display_effects_only = 1)
  
  summarize_MCMC_OutcomeEq(res$dataY, res$MCMC_Y, display_effects_individually = 0, display_effects_only = 1)  
}


#--------------------- Functions to initialize the param vectors with true values -------------------#
initialize_with_true_paramp0 <- function(paramp0, true_paramp0, r_pl, TT) {
  k_y1 <- length(paramp0)
  
  for(l in 1:k_y1) {
    paramp0[[l]]$beta <- true_paramp0[[l]]$beta
    paramp0[[l]]$alpha_i <- true_paramp0[[l]]$alpha_i
    paramp0[[l]]$mu_alpha_i <- true_paramp0[[l]]$mu_alpha_i
    paramp0[[l]]$Sigma_alpha_i <- true_paramp0[[l]]$Sigma_alpha_i
    paramp0[[l]]$xi_t <- true_paramp0[[l]]$xi_t
    paramp0[[l]]$gamma_i <- true_paramp0[[l]]$gamma_i
    paramp0[[l]]$f_p_t <- true_paramp0[[l]]$f_p_t
    if(r_pl[l] > ncol(paramp0[[l]]$f_p_t)) {
      add_zero_cols <- matrix( rep(0, TT*(r_pl[l] - ncol(paramp0[[l]]$f_p_t)  )), nrow = TT, ncol = r_pl[l] - ncol(paramp0[[l]]$f_p_t))
      paramp0[[l]]$f_p_t <- cbind(paramp0[[l]]$f_p_t, add_zero_cols)
      
    }
    
    if(r_pl[l] > ncol(paramp0[[l]]$gamma_i)) {
      add_zero_cols <- matrix( rep(0, N*(r_pl[l] - ncol(paramp0[[l]]$gamma_i)  )), nrow = N, ncol = r_pl[l] - ncol(paramp0[[l]]$gamma_i))
      paramp0[[l]]$gamma_i <- cbind(paramp0[[l]]$gamma_i, add_zero_cols)
    }
    
    paramp0[[l]]$sigma2 <- true_paramp0[[l]]$sigma2
    paramp0[[l]]$sigma2e <- true_paramp0[[l]]$sigma2e
    paramp0[[l]]$phi_xi <- diag(true_paramp0[[l]]$phi_xi)
    
    if(r_pl[l] > length(true_paramp0[[l]]$phi_f)) {
      add_zeros <- rep(0, r_pl[l] - length(true_paramp0[[l]]$phi_f))
      paramp0[[l]]$phi_f <- diag(c(true_paramp0[[l]]$phi_f, add_zeros))
    }
  }

  return(paramp0)
}
initialize_with_true_paramy0 <- function(paramy0, true_paramy0, r_y, TT) {
  
  paramy0$beta <- true_paramy0$beta
  paramy0$alpha_i <- true_paramy0$alpha_i
  paramy0$mu_alpha_i <- true_paramy0$mu_alpha_i
  paramy0$Sigma_alpha_i <- true_paramy0$Sigma_alpha_i
  paramy0$xi_t <- true_paramy0$xi_t
  paramy0$gamma_i <- true_paramy0$gamma_i
  paramy0$f_t <- true_paramy0$f_t
  
  if(r_y > ncol(paramy0$f_t)) {
    add_zero_cols <- matrix( rep(0, TT*(r_y - ncol(paramy0$f_t)  )), nrow = TT, ncol = r_y - ncol(paramy0$f_t))
    paramy0$f_t <- cbind(paramy0$f_t, add_zero_cols)
  }
  
  if(r_y > ncol(paramy0$gamma_i)) {
    add_zero_cols <- matrix( rep(0, N*(r_y - ncol(paramy0$gamma_i)  )), nrow = N, ncol = r_y - ncol(paramy0$gamma_i))
    paramy0$gamma_i <- cbind(paramy0$gamma_i, add_zero_cols)
  }
  
  paramy0$phi_delta <- true_paramy0$phi_delta
  paramy0$sigma2 <- true_paramy0$sigma2
  paramy0$sigma2e <- true_paramy0$sigma2e
  paramy0$phi_xi <- diag(true_paramy0$phi_xi)
  
  if (r_y > length(true_paramy0$phi_f)) {
    add_zeros <- rep(0, r_y - length(true_paramy0$phi_f))
    paramy0$phi_f <- diag(c(true_paramy0$phi_f, add_zeros))
  }

  return(paramy0)
}

### BCEndo the main function.

BCEndo <- function(data,   
                    index,
                    OutcomeEqInfo,
                    MediatorEqInfo,
                    NBURN,
                    THIN,
                    NCOLLECT)  {
  
  if(("tidyverse" %in% rownames(installed.packages()) == FALSE) |
     ("mvtnorm" %in% rownames(installed.packages())) == FALSE |    
     ("HDInterval" %in% rownames(installed.packages())) == FALSE) {
    stp("BCEndo depends on the following packages: tidyverse, mvtnorm, and HDInterval.\n Please install any missing packages to run BCEndo.")
  }

  requireNamespace("tidyverse", quietly = TRUE)
  requireNamespace("mvtnorm", quietly = TRUE)
  requireNamespace("HDInterval", quietly = TRUE)
  
  ####################### Checking the arguments ######################
  
  if(as.numeric(R.version$major) < 4) {
    stop("R version 4.1.0 or later is required. Please update R software.")
  } else if (as.numeric(R.version$minor) < 1.0) {
    stop("R version 4.1.0 or later is required. Please update R software.")
  }
  
  varnames <- colnames(data)
  
  if(sum(varnames == index[1]) == 0) stop("The unit index is not found in the dataset")
  if(sum(varnames == index[2]) == 0) stop("The time index is not found in the dataset")
  if(sum(varnames == OutcomeEqInfo$Y) == 0 ) stop("The outcome variable is not found in the dataset. Check OutcomeEqInfo$Y")
  if(sum(varnames == OutcomeEqInfo$D) == 0) stop("The treatment indicator variable is not found in the dataset. Check OutcomeEqInfo$D")
  
  if(!is.null(OutcomeEqInfo$Xp)) 
    if(  sum(sapply(OutcomeEqInfo$Xp, `%in%`, varnames)) < length(OutcomeEqInfo$Xp)  ) stop("One or more mediators are not found in the dataset. Check OutcomeEqInfo$Xp")
  
  if(!is.null(OutcomeEqInfo$Xq)) 
    if(  sum(sapply(OutcomeEqInfo$Xq, `%in%`, varnames)) < length(OutcomeEqInfo$Xq)  ) stop("One or more exogenous covariates of the outcome equation are not found in the dataset. Check OutcomeEqInfo$Xq")
  
  if(!is.null(OutcomeEqInfo$Xdelta)) 
    if( sum(sapply(OutcomeEqInfo$Xdelta, `%in%`, varnames)) < length(OutcomeEqInfo$Xdelta) ) stop("One or more moderators of the direct effect are not found in the dataset. Check OutcomeEqInfo$Xdelta")
  

  if(sum(varnames == OutcomeEqInfo$treat) == 0) stop("The identifier for treatment units is not found in the dataset. Check OutcomeEqInfo$treat")
  if(OutcomeEqInfo$nFactor < 3) stop("The minumum number of factors is 3.")
  if(OutcomeEqInfo$re != "unit" & OutcomeEqInfo$re != "time" & OutcomeEqInfo$re != "both"  & OutcomeEqInfo$re != "none") stop("The randome effect should be \"unit\", \"time\", \"both\", or \"none\". Check OutcomeEqInfo$re")
  if(OutcomeEqInfo$estimate_individual_coefs != 0 & OutcomeEqInfo$estimate_individual_coefs != 1 ) stop("OutcomeEqInfo$estimate_individual_coefs should be 0 or 1.")
  if(OutcomeEqInfo$estimate_phi_delta != 0 & OutcomeEqInfo$estimate_phi_delta != 1 ) stop("OutcomeEqInfo$estimate_phi_delta should be 0 or 1.")
  if(OutcomeEqInfo$factor_selection_method != "spike-slab" & OutcomeEqInfo$factor_selection_method != "horseshoe") stop("The variable selection method should be either \"spike-slab\" or \"horseshoe\".")
  
  if(!is.null(OutcomeEqInfo$Xp)) {
    
    if(length(MediatorEqInfo$P) != length(OutcomeEqInfo$Xp)) stop("The length of MediatorEqInfo$P should be the same to the length of OutcomeEqInfo$Xp")
    if(sum(unlist(MediatorEqInfo$P) == OutcomeEqInfo$Xp) < length(OutcomeEqInfo$Xp) ) stop("The mediators in MediatorEqInfo$P do not match with the mediators in OutcomeEqInfo$Xp.")
    if(length(MediatorEqInfo$X) != length(OutcomeEqInfo$Xp)) stop("The length of MediatorEqInfo$X should be the same to the length of OutcomeEqInfo$Xp")
    if(sum(  sapply(  unlist(MediatorEqInfo$X), `%in%`, varnames   ) ) < length(unlist(MediatorEqInfo$X))   ) stop("Some of the variables in MediatorEqInfo$X are not found in the dataset.")
    if(  length(MediatorEqInfo$nFactor) != length(OutcomeEqInfo$Xp)   )  stop("The legnth of MediatorEqInfo$nFactor is different from the number of mediators in OutcomeEqInfo$Xp.")
    if(sum(MediatorEqInfo$nFactor < 3)) stop("The minimum number of factors is 3.")
    if(length(MediatorEqInfo$re) !=  length(OutcomeEqInfo$Xp) ) stop("The length of MediatorEqInfo$re should be the same to the number of mediators in OutcomeEqInfo$Xp.")
    if(length(MediatorEqInfo$estimate_individual_coefs) !=  length(OutcomeEqInfo$Xp) ) stop("The length of MediatorEqInfo$estimate_individual_coefs should be the same to the number of mediators in OutcomeEqInfo$Xp.")
    
    if(length(MediatorEqInfo$impute_p0_mis) !=  length(OutcomeEqInfo$Xp) ) stop("The length of MediatorEqInfo$impute_p0_mis should be the same to the number of mediators in OutcomeEqInfo$Xp.")
    
    if(length(MediatorEqInfo$factor_selection_method) !=  length(OutcomeEqInfo$Xp) ) stop("The length of MediatorEqInfo$factor_selection_method should be the same to the number of mediators in OutcomeEqInfo$Xp.")
    
    for (l in 1:length(OutcomeEqInfo$Xp)) {
      if(MediatorEqInfo$re[l] != "unit" & MediatorEqInfo$re[l] != "time" & MediatorEqInfo$re[l] != "both" & MediatorEqInfo$re[l] != "none")   stop("The randome effect should be \"unit\", \"time\", \"both\", or \"none\". Check MediatorEqInfo$re")
      if(MediatorEqInfo$estimate_individual_coefs[l] != 0 & MediatorEqInfo$estimate_individual_coefs[l] != 1)   stop("MediatorEqInfo$estimate_individual_coefs should be 0 or 1")

      if(MediatorEqInfo$impute_p0_mis[l] != 0 & MediatorEqInfo$impute_p0_mis[l] != 1)   stop("MediatorEqInfo$impute_p0_mis should be 0 or 1")   
      
      if(MediatorEqInfo$estimate_phi_delta[l] != 0 & MediatorEqInfo$estimate_phi_delta[l] != 1)   stop("MediatorEqInfo$estimate_phi_delta should be 0 or 1")   
      
      if(MediatorEqInfo$factor_selection_method[l] != "spike-slab" & MediatorEqInfo$factor_selection_method[l] != "horseshoe" ) 
        stop("The variable selection method should be either \"spike-slab\" or \"horseshoe\".")
    }
  }
  
  if(NBURN < 0) stop("NBURN should be a positive number.")
  if(THIN < 1) stop("NBURM should be greater than zero.")
  if(NCOLLECT < 1) stop("NCOLLECT should grater than zero.")
  
  ####################### Data Prep ######################

  data <- as.data.frame(data)
  data_ordered <- data |> arrange(desc(OutcomeEqInfo$treat), index[1], index[2])   
  id_mapping <- data_ordered |> filter(eval(parse(text = index[2])) == 1) |> select(index[1]) |> mutate(id = 1:n())
  
  #<------------dataY------------------->
  datY <- data_ordered |> left_join(id_mapping, by = index[1]) |> 
    rename(time = index[2], treat = OutcomeEqInfo$treat, D = OutcomeEqInfo$D, Y = OutcomeEqInfo$Y) |> 
    select(id, time, Y, D, treat, OutcomeEqInfo$Xp, OutcomeEqInfo$Xq, OutcomeEqInfo$Xdelta)
  
  tt <- datY |> group_by(id) |> summarize(tt = mean(treat))
  N_co <- sum(1 - tt$tt)
  N_tr <- sum(tt$tt)
  N <- N_tr + N_co
  TT <- max(datY$time)
  T0 <- datY |> group_by(id) |> summarize(T0 = TT - sum(D))
  
  T0$T0[T0$T0 == TT] <- Inf
  T0[T0 == -1] <- Inf
  T0 <- T0$T0 |> unlist() |> unname()
  
  Xp <- datY |> select(OutcomeEqInfo$Xp)
  Xq <- datY |> select(OutcomeEqInfo$Xq)
  Xq <- cbind(Xq, 1)
  ncol_Xq <- ncol(Xq)
  colnames(Xq)[ncol_Xq] <- "intercept"
  k_y1 <- ncol(Xp)
  k_y2 <- ncol(Xq) 
  k_y <- k_y1 + k_y2
  
  if(is.null(OutcomeEqInfo$Xdelta)) {
    Xdelta <- matrix(, nrow = nrow(datY), ncol = 0)  
  } else {
    Xdelta <- datY |> select(OutcomeEqInfo$Xdelta)
  }
  Xdelta <- cbind(Xdelta, 1)
  ncol_Xdelta <- ncol(Xdelta)
  colnames(Xdelta)[ncol_Xdelta] <- "intercept"
  
  Xdelta <- as.matrix(Xdelta)
  k_y_phi <- ncol(Xdelta)
  
  treated_unit_ids <- 1:N_tr
  control_unit_ids <- (N_tr+1):N
  
  treated_idx_by_unit <- ctrl_idx_by_unit <- vector(mode = "list", length = N) 
  for(i in 1:N) {
    treated_idx_by_unit[[i]] <- datY |> filter(id == i, D == 1) |> select(time) |> unlist() |> unname()
    ctrl_idx_by_unit[[i]] <- datY |> filter(id == i, D == 0) |> select(time) |> unlist() |> unname()
  }
  
  treated_idx <- which(datY$D == 1)
  ctrl_idx <- which(datY$D == 0)
  
  datY <- as.data.frame(datY)
  Xp <- as.data.frame(Xp)
  Xq <- as.data.frame(Xq)
  Xdelta <- as.data.frame(Xdelta)
  
  treated_unit_ids_original <- id_mapping[index[1]][1:N_tr,]
  control_unit_ids_original <- id_mapping[index[1]][(N_tr+1):(N),]
  
  dataY <- list(dat = datY, Xp = Xp, Xq = Xq, Xdelta = Xdelta,
                TT = TT, N = N, N_co = N_co, N_tr = N_tr, T0 = T0,
                k_y = k_y, k_y1 = k_y1, k_y2 = k_y2, k_y_phi = k_y_phi, 
                treated_unit_ids = treated_unit_ids, control_unit_ids = control_unit_ids,
                treated_idx_by_unit = treated_idx_by_unit, ctrl_idx_by_unit = ctrl_idx_by_unit,
                treated_idx = treated_idx, ctrl_idx = ctrl_idx,
                treated_unit_ids_original = treated_unit_ids_original,
                control_unit_ids_original = control_unit_ids_original)
  
  
  #<------------dataP------------------->
  if(!is.null(OutcomeEqInfo$Xp)) {   # relevant only when mediators exist
    
    k_pl <- vector(mode = "numeric", length = k_y1)
    dataP <- vector(mode = "list", length = k_y1)
    
    for(l in 1:k_y1) {
      datP <- data_ordered |> left_join(id_mapping, by = index[1]) |> 
        rename(time = index[2], treat = OutcomeEqInfo$treat, D = OutcomeEqInfo$D, p = MediatorEqInfo$P[[l]])|> 
        select(id, time, p, D, treat, MediatorEqInfo$X[[l]])
      
      Xp <- datP |> select(   MediatorEqInfo$X[[l]]   )
      Xp <- cbind(Xp, 1)
      Xp_ncol <- ncol(Xp)
      colnames(Xp)[Xp_ncol] <- "intercept"
      k_pl <- ncol(Xp)
      datP <- as.data.frame(datP)
      Xp <- as.data.frame(Xp)
      
      if(  is.null(MediatorEqInfo$Xdelta[[l]])   ) {
        Xdelta <- matrix(, nrow = nrow(datP), ncol = 0)  
      } else {
        Xdelta <- datP |> select(MediatorEqInfo$Xdelta[[l]])
      }
      Xdelta <- cbind(Xdelta, 1)
      ncol_Xdelta <- ncol(Xdelta)
      colnames(Xdelta)[ncol_Xdelta] <- "intercept"
      
      Xdelta <- as.matrix(Xdelta)
      
      dataP[[l]] <- list(dat = datP, Xp = Xp, Xdelta = Xdelta)
      
      dataP[[l]][["TT"]] <- TT
      dataP[[l]][["N"]] <- N
      dataP[[l]][["N_co"]] <- N_co
      dataP[[l]][["N_tr"]] <- N_tr
      dataP[[l]][["T0"]] <- T0
      dataP[[l]][["k_y"]] <- k_y
      dataP[[l]][["k_y1"]] <- k_y1
      dataP[[l]][["k_y2"]] <- k_y2
      dataP[[l]][["k_pl"]] <- k_pl
      dataP[[l]][["treated_unit_ids"]] <- treated_unit_ids
      dataP[[l]][["control_unit_ids"]] <- control_unit_ids
      
      dataP[[l]][["treated_idx_by_unit"]] <- treated_idx_by_unit
      dataP[[l]][["ctrl_idx_by_unit"]] <- ctrl_idx_by_unit
      dataP[[l]][["treated_idx"]] <- treated_idx
      dataP[[l]][["ctrl_idx"]] <- ctrl_idx
      dataP[[l]][["treated_unit_ids_original"]]  <- treated_unit_ids_original
      dataP[[l]][["control_unit_ids_original"]]  <- control_unit_ids_original
    }
  }
  

  ####################### Estimation ######################
  
  res <- doit(dataY, 
              dataP,
              OutcomeEqInfo = OutcomeEqInfo,
              MediatorEqInfo = MediatorEqInfo,
              NBURN = NBURN,
              THIN = THIN,
              NCOLLECT = NCOLLECT)
  
  return(res)
}

doit <- function(dataY, 
                 dataP,
                 OutcomeEqInfo = OutcomeEqInfo,
                 MediatorEqInfo = MediatorEqInfo,
                 NBURN = NBURN,
                 THIN = THIN,
                 NCOLLECT = NCOLLECT) {
  
  ################## Prep for Gibbs Sampler   ################## 
  
  # Reading data information
  N <- dataY$N  # total number of units
  N_tr <- dataY$N_tr  # number of treated units
  N_co <- N - N_tr  # number of control units
  TT <- dataY$TT    # number of time periods
  T0 <- dataY$T0  # # number of control periods
  
  k_y <- dataY$k_y  
  k_y1 <- dataY$k_y1  # number of covariates that vary with treatment statuses
  k_y2 <- dataY$k_y2  # number of covariates that do not vary with treatment statuses
  k_y_phi <- dataY$k_y_phi  # number of covariates that explain the variation of delta_y, the direct treatment effect
  
  k_pl <- k_pl_phi <- vector(mode = "numeric", length = k_y1)
  
  if(k_y1 > 0) {
    for(l in 1:k_y1) k_pl[l] <- ncol(dataP[[l]]$Xp)
    for(l in 1:k_y1) k_pl_phi[l] <- ncol(dataP[[l]]$Xdelta)
  }
  
  
  ## set the number of factors (and factor loadings)
  r_y <- OutcomeEqInfo$nFactor
  
  if (k_y1 > 0) r_pl <- MediatorEqInfo$nFactor
  
  ## Initialize parameters for p
  if (k_y1 > 0) {
    paramp0 <- vector(mode = "list", length = k_y1)
    for (l in 1:k_y1) {
      beta_p <- rep(1, k_pl[l])
      alpha_p_i <- matrix(rep(0, N*k_pl[l]), nrow = N, ncol = k_pl[l])
      mu_alpha_p <- rep(0, k_pl[l])  # overparam mean of alpha
      Sigma_alpha_p <- diag(k_pl[l])
      xi_p_t <- matrix(rep(0, TT*k_pl[l]), nrow = TT, ncol = k_pl[l])
      gamma_p_i <- matrix(rep(0, N*r_pl[l]), nrow = N, ncol = r_pl[l])
      mu_gamma_p <- rep(0, r_pl[l])  # overparam mean of gamma
      Sigma_gamma_p <- diag(r_pl[l])
      f_p_t <- matrix(rep(0, TT*r_pl[l]), nrow = TT, ncol = r_pl[l])
      sigma2_p <- 1
      phi_xi <- diag(k_pl[l])*0
      phi_f <- diag(r_pl[l])*0.7
      tau2_p <- 1000
      sigma2_p_e <- diag(k_pl[l])
      pi_p <- rep(1, r_pl[l])
      theta_p <- 0.5
      s_p <- 1
      p0_mis <- dataP[[l]]$dat$p  # initialize with observed data
      phi_delta_pl <- rep(0, k_pl_phi[l])
      sigma2_eta_pl <- 1
      
      ## horseshoe prior params
      tau <- rep(1, N)
      lambda <- matrix(rep(1, N*r_pl[l]), nrow = N, ncol = r_pl[l])
      
      paramp0[[l]] <- list(beta = beta_p, alpha_i = alpha_p_i, xi_t = xi_p_t, 
                           gamma_i = gamma_p_i, f_p_t = f_p_t, sigma2 = sigma2_p, tau2 = tau2_p,
                           sigma2e = sigma2_p_e, phi_xi = phi_xi, phi_f = phi_f,
                           pi = pi_p, theta = theta_p, s = s_p, mu_alpha = mu_alpha_p, Sigma_alpha = Sigma_alpha_p,
                           p0_mis = p0_mis, phi_delta_pl = phi_delta_pl, sigma2_eta_pl = sigma2_eta_pl,
                           delta = rep(0, N*TT), tau = tau, lambda = lambda)
    }
  } else {
    paramp0 <- 0  # placeholder for draw_y0_mis_cpp()
  }
  
  # initialize parameters for y
  beta_y <- rep(1, k_y)
  alpha_yi <- matrix(rep(0, N*k_y), nrow = N, ncol = k_y)
  mu_alpha_yi <- rep(0, k_y)  # overparam mean of alpha
  Sigma_alpha_yi <- diag(k_y)
  xi_yt <- matrix(rep(0, TT*k_y), nrow = TT, ncol = k_y)
  gamma_yi <- matrix(rep(0, N*r_y), nrow = N, ncol = r_y)
  f_yt <- matrix(rep(0, TT*r_y), nrow = TT, ncol = r_y)
  sigma2_y <- 1
  phi_xi <- diag(k_y)*0
  phi_f <- diag(r_y)*0.7
  tau2_y <- 100
  sigma2_y_e <- diag(k_y)
  pi_y <- rep(0, r_y)
  theta_y <- 0.5
  s_y <- 1
  y0_mis <- rep(0, N*TT)
  eps <- rep(0, N*TT)
  phi_delta_y <- rep(0, k_y_phi)  
  sigma2_eta_y <- 1
  
  ## horseshoe prior
  tau <- rep(1, N)
  lambda <- matrix(rep(1, N*r_y), nrow = N, ncol = r_y)
  
  paramy0 <- list(beta = beta_y, alpha_i = alpha_yi, xi_t = xi_yt, 
                  gamma_i = gamma_yi, f_t = f_yt, sigma2 = sigma2_y, tau2 = tau2_y,
                  sigma2e = sigma2_y_e, phi_xi = phi_xi, phi_f = phi_f,
                  pi = pi_y, theta = theta_y, s = s_y, mu_alpha_i = mu_alpha_yi, Sigma_alpha_i = Sigma_alpha_yi,
                  y0_mis = y0_mis, eps = eps, tte = rep(0, N*TT), delta = rep(0, N*TT), mte = rep(0, N*TT),
                  phi_delta = phi_delta_y, sigma2_eta = sigma2_eta_y,
                  tau = tau, lambda = lambda)
  
  ## MCMC Settings
  NCOLLECT <- NCOLLECT
  NBURN <- NBURN
  NGIBBS <- NBURN + NCOLLECT*THIN
  
  if(k_y1 > 0) {
    MCMC_p_beta <- MCMC_p_alpha_i <- MCMC_p_mu_alpha <- MCMC_p_xi <- MCMC_p_gamma_i <- MCMC_p_f <- MCMC_p_gamma_i <- 
      MCMC_p_phi_xi <- MCMC_p_phi_f <- MCMC_p_sigma2_e <- MCMC_p_sigma2_eps <- MCMC_p_pi <- 
      MCMC_p_theta <- MCMC_p_tau2 <- MCMC_p_s <- 
      MCMC_p_p0_mis <- MCMC_p_delta <- MCMC_p_phi_delta <- MCMC_p_sigma2_eta <- 
      MCMC_p_tau <- MCMC_p_lambda <- vector(mode = "list", length = k_y1)
    
    for(l in 1:k_y1) {
      MCMC_p_beta[[l]] <- matrix(0, nrow = NCOLLECT, ncol = k_pl[l])  
      MCMC_p_alpha_i[[l]] <- array(0, dim = c(N, k_pl[l], NCOLLECT))
      MCMC_p_mu_alpha[[l]] <- matrix(0, NCOLLECT, k_pl[l])
      MCMC_p_xi[[l]] <- array(0, dim = c(TT, k_pl[l], NCOLLECT))
      MCMC_p_f[[l]] <- array(0, dim = c(TT, r_pl[l], NCOLLECT))
      MCMC_p_gamma_i[[l]] <- array(0, dim = c(N, r_pl[l], NCOLLECT))  
      MCMC_p_phi_xi[[l]] <- matrix(0, nrow = NCOLLECT, ncol = k_pl[l])
      MCMC_p_phi_f[[l]] <- matrix(0, nrow = NCOLLECT, ncol = r_pl[l])
      MCMC_p_sigma2_e[[l]] <- matrix(0, nrow = NCOLLECT, ncol = k_pl[l])
      MCMC_p_sigma2_eps[[l]] <- numeric(length = NCOLLECT)
      MCMC_p_pi[[l]] <- matrix(0, NCOLLECT, r_pl[l])
      MCMC_p_theta[[l]] <- MCMC_p_tau2[[l]] <- MCMC_p_s[[l]] <- vector(length = NCOLLECT)
      MCMC_p_p0_mis[[l]] <- matrix(0, NCOLLECT, N*TT)
      MCMC_p_delta[[l]] <- matrix(0, NCOLLECT, N*TT)
      
      MCMC_p_phi_delta[[l]] <- matrix(0, NCOLLECT, k_pl_phi[l])  
      MCMC_p_sigma2_eta[[l]] <- rep(0, NCOLLECT)
      
      MCMC_p_tau[[l]] <- matrix(0, NCOLLECT, N)  
      MCMC_p_lambda[[l]] <- array(0, dim = c(N, r_pl[l], NCOLLECT))  
    }
  }
  
  MCMC_y_beta <- matrix(0, nrow = NCOLLECT, ncol = k_y)
  MCMC_y_alpha_i <- array(0, dim = c(N, k_y, NCOLLECT))
  MCMC_y_mu_alpha <- matrix(0, NCOLLECT, k_y)
  MCMC_y_xi <- array(0, dim = c(TT, k_y, NCOLLECT))
  MCMC_y_f <- array(0, dim = c(TT, r_y, NCOLLECT))
  MCMC_y_gamma_i <- array(0, dim = c(N, r_y, NCOLLECT))
  MCMC_y_mu_gamma_i <- matrix(0, NCOLLECT, r_y)
  MCMC_y_phi_xi <- matrix(0, nrow = NCOLLECT, ncol = k_y)
  MCMC_y_phi_f <- matrix(0, nrow = NCOLLECT, ncol = r_y)
  MCMC_y_sigma2_e <- matrix(0, nrow = NCOLLECT, ncol = k_y)
  MCMC_y_sigma2_eps <- numeric(length = NCOLLECT)
  MCMC_y_pi <- matrix(0, NCOLLECT, r_y)
  MCMC_y_theta <- MCMC_y_tau2 <- MCMC_y_s <- vector(length = NCOLLECT)
  MCMC_y_y0_mis <- matrix(0, NCOLLECT, N*TT)
  MCMC_y_tte <- matrix(0, NCOLLECT, N*TT)
  MCMC_y_mte<- matrix(0, NCOLLECT, N*TT)
  MCMC_y_delta <- matrix(0, NCOLLECT, N*TT)
  MCMC_y_phi_delta <- matrix(0, NCOLLECT, k_y_phi)  
  MCMC_y_sigma2_eta <- rep(0, NCOLLECT)
  MCMC_y_tau <- matrix(0, nrow = NCOLLECT, ncol = N)  
  MCMC_y_lambda <- array(0, dim = c(N, r_y, NCOLLECT))  
  
  if(k_y1 > 0) {
    re_p <- MediatorEqInfo$re
    estimate_individual_coefs_p <- MediatorEqInfo$estimate_individual_coefs
    estimate_time_varying_coefs_p <- MediatorEqInfo$estimate_time_varying_coefs
    impute_p0_mis <- MediatorEqInfo$impute_p0_mis
    estimate_phi_delta_p <- MediatorEqInfo$estimate_phi_delta
    factor_selection_method_p <- MediatorEqInfo$factor_selection_method
  }
  
  re_y <- OutcomeEqInfo$re
  estimate_individual_coefs_y <- OutcomeEqInfo$estimate_individual_coefs
  estimate_time_varying_coefs_y <- OutcomeEqInfo$estimate_time_varying_coefs
  estimate_phi_delta_y <- OutcomeEqInfo$estimate_phi_delta
  factor_selection_method_y <- OutcomeEqInfo$factor_selection_method
  
  
  ################## Running Gibbs Sampler   ################## 
  
  for(ng in 1:NGIBBS) {
    
    if (ng %% 10 == 0) cat("ng: ", ng, "\n")
    
    ###### estimate mediator eq ######
    if(!is.null(OutcomeEqInfo$Xp)) {    
      for (l in 1:k_y1) {
        datP <- dataP[[l]]
        paramp <- paramp0[[l]]
        
        # Step 1-1
        beta <- draw_beta_p0_l_cpp(datP, paramp)
        paramp$beta <- beta 
        
        if(   (re_p[l] == "unit" | re_p[l] == "both") & estimate_individual_coefs_p[l] == 1   ) {   # one-shot estimation of intercept and coefficients
          alpha_i <- draw_alpha_p0_i_l_overparam_with_intercept_cpp(datP, paramp)
          
          paramp$alpha_i <- alpha_i$alpha_i
          paramp$mu_alpha <- alpha_i$mu_alpha
          paramp$Sigma_alpha <- diag(as.numeric(alpha_i$Sigma_alpha), nrow = k_pl[l], ncol = k_pl[l])
          
        } else if (  (re_p[l] == "unit" | re_p[l] == "both") & estimate_individual_coefs_p[l] == 0    ) {
          intercept_i <- draw_individual_intercept_p0_i_l_overparam_cpp(datP, paramp)
          
          i0 <- k_pl[l]
          paramp$alpha_i[,i0] <- intercept_i$intercept_i
          paramp$mu_alpha[i0] <- intercept_i$mu_intercept
          paramp$Sigma_alpha[i0, i0] <-  intercept_i$Sigma_intercept
        } else if ( (  re_p[l] == "none" | re_p[l] == "time") & estimate_individual_coefs_p[l] == 1  & ncol(dataP[[l]]$Xp) > 1 ) {  # should be more than one column to estimate this. one column is intercept
          alpha_i <- draw_alpha_p0_i_l_overparam_cpp(datP, paramp)
          
          i0 <- 1:(k_pl[l] - 1)
          paramp$alpha_i[, i0] <- alpha_i$alpha_i[, i0]
          paramp$mu_alpha[i0] <- alpha_i$mu_alpha[i0]
          paramp$Sigma_alpha[i0, i0] <- diag(alpha_i$Sigma_alpha[i0], nrow = length(i0), ncol = length(i0))
        } 
  
        if(   (re_p[l] == "time" | re_p[l] == "both") & estimate_time_varying_coefs_p[l] == 1   ) {   # one-shot estimation of intercept and coefficients
          paramp$xi_t <- draw_xi_p0_t_l_with_intercept_cpp(datP, paramp)
          paramp$sigma2e <- draw_sigma2_e_p0_j_l_cpp(datP, paramp)
        } else if (  (re_p[l] == "time" | re_p[l] == "both") & estimate_time_varying_coefs_p[l] == 0    ) {
          res <- draw_xi_p0_t_l_intercept_only_cpp(datP, paramp)
          paramp$xi_t <- cbind(matrix(0, nrow = nrow(res), ncol = k_pl[l] - 1), res)
          paramp$sigma2e <- draw_sigma2_e_p0_j_l_cpp(datP, paramp)
        } else if (  ( re_p[l] == "none"  | re_p[l] == "unit") & estimate_time_varying_coefs_p[l] == 1  & ncol(dataP[[l]]$Xp) > 1 ) {  # should be more than one column to estimate this. one column is intercept
          res <- draw_xi_p0_t_l_cpp(datP, paramp)
          paramp$xi_t <- cbind(res, 0)   # 0 is for intercept
          paramp$sigma2e <- draw_sigma2_e_p0_j_l_cpp(datP, paramp)
        } 
  
        f_p <- draw_f_p0_t_l_cpp(datP, paramp)
        if (r_pl[l] > 0) paramp$f_p_t <- f_p
  
        if(factor_selection_method_p[l] == "spike-slab") {
          gamma_i <- draw_gamma_p0_i_l_cpp(datP, paramp)
          paramp$gamma_i <- gamma_i
  
          pi_ <- draw_pi_p0_j_l_cpp(datP, paramp)
          paramp$pi <- pi_$pi
          paramp$gamma_i <- pi_$gamma_i
  
          theta <- draw_theta_p0_l_cpp(datP, paramp)
          paramp$theta <- theta
  
          tau2 <- draw_tau2_p0_l_cpp(datP, paramp)
          paramp$tau2 <- tau2
  
          s <- draw_s_p0_l_cpp(datP, paramp)
          paramp$s <- s
        } else {   ## horseshoe
          gamma_i <- draw_gamma_p0_i_l_hs_cpp(datP, paramp)
  
          paramp$gamma_i <- gamma_i$gamma
          paramp$tau <- gamma_i$tau
          paramp$lambda <- gamma_i$lambda
        } 
  
        phi_f <- draw_phi_f_p0_j_l_cpp(datP, paramp)
        paramp$phi_f <- phi_f
  
        sigma2 <- draw_sigma2_eps_p0_l_cpp(datP, paramp)
        paramp$sigma2 <- sigma2
  
        # Step 1-2
        if (impute_p0_mis[l] == 1) {
          p0_mis <- draw_p0_mis_cpp(datP, paramp)
          paramp$p0_mis <- as.numeric(p0_mis)
        }
  
        delta_p <- draw_p0_delta_cpp(datP, paramp)
        paramp$delta <- as.numeric(delta_p)
        
        if(estimate_phi_delta_p[l] == 1) {
          phi_delta_p <- draw_phi_delta_p_cpp(datP, paramp, 0)
          paramp$phi_delta <- as.numeric(phi_delta_p[[1]]);
          
          sigma2_eta_p <- draw_sigma2_eta_p_cpp(datP, paramp, 0)
          paramp$sigma2_eta <- sigma2_eta_p[[1]]
        }
        
  
        ## (don't forget to update paramp0) update paramp0 with the newly drawn parameters because paramp0 is accessed at the beginning
        paramp0[[l]] <- paramp
      }
   }
    
    ###### estimate outcome eq ######
    
    ## Step 2-1
    beta_y <- draw_beta_y0_cpp(dataY, paramy0)
    paramy0$beta <- beta_y[[1]]
    
    if (  (re_y == "unit" | re_y == "both")  &  estimate_individual_coefs_y == 1 ) {
      alpha_y <- draw_alpha_y0_i_overparam_with_intercept_cpp(dataY, paramy0)
      
      paramy0$alpha_i <- alpha_y$alpha_i
      paramy0$mu_alpha_i <- alpha_y$mu_alpha
      paramy0$Sigma_alpha_i <- diag(  as.numeric(alpha_y$Sigma_alpha), nrow = k_y, ncol = k_y    )
    } else if (  (re_y == "unit" | re_y == "both")  &  estimate_individual_coefs_y == 0  ) {
      intercept_y <- draw_individual_intercept_y0_overparam_cpp(dataY, paramy0)
      
      i0 <- k_y
      paramy0$alpha_i[,i0] <- intercept_y$intercept_i
      paramy0$mu_alpha_i[i0] <- intercept_y$mu_intercept
      paramy0$Sigma_alpha_i[i0, i0] <-  intercept_y$Sigma_intercept
    } else if (   (re_y == "none" | re_y == "time")  &  estimate_individual_coefs_y == 1  ) {
      alpha_y <- draw_alpha_y0_i_overparam_cpp(dataY, paramy0)
      
      i0 <- 1:(k_y - 1)
      paramy0$alpha_i[, i0] <- alpha_y$alpha_i[, i0]
      paramy0$mu_alpha_i[i0] <- alpha_y$mu_alpha[i0]
      nrow <- ncol <- length(i0)
      paramy0$Sigma_alpha_i[i0, i0] <- diag(  alpha_y$Sigma_alpha[i0], nrow = nrow, ncol = ncol    )
    }
    
    if ((re_y == "time" | re_y == "both")  & estimate_time_varying_coefs_y == 1 ) {
      res <- draw_xi_y0_t_with_intercept_cpp(dataY, paramy0)  # xi_f should precede gamma
      paramy0$xi_t <- t(res$xi)
      
      sigma2e_y <- draw_sigma2_e_y0_j_cpp(dataY, paramy0)
      paramy0$sigma2e <- sigma2e_y[[1]]
    } else if ((re_y == "time" | re_y == "both")  &  estimate_time_varying_coefs_y == 0  ) {
      res <- draw_xi_y0_t_intercept_only_cpp(dataY, paramy0)  # xi_f should precede gamma
      paramy0$xi_t <- cbind(matrix(0, nrow = nrow(  t(res$xi)  ), ncol = k_y - 1), t(res$xi)) 
      
      sigma2e_y <- draw_sigma2_e_y0_j_cpp(dataY, paramy0)
      paramy0$sigma2e <- sigma2e_y[[1]]
    } else if ((re_y == "none" | re_y == "unit")  &  estimate_time_varying_coefs_y == 1  ) {
      res <- draw_xi_y0_t_cpp(dataY, paramy0)  # xi_f should precede gamma
      paramy0$xi_t <- cbind(t(res$xi), 0)  # 0 is place for intercept
      
      sigma2e_y <- draw_sigma2_e_y0_j_cpp(dataY, paramy0)
      paramy0$sigma2e <- sigma2e_y[[1]]
    }
    
    f_y <- draw_f_y0_t_cpp(dataY, paramy0)  # xi_f should precede gamma
    paramy0$f_t <- t(f_y$f)

    if(factor_selection_method_y == "spike-slab") {
      gamma_y <- draw_gamma_y0_i_cpp(dataY, paramy0)
      paramy0$gamma_i <- gamma_y[[1]];

      pi_y <- draw_pi_y0_j_cpp(dataY, paramy0)
      paramy0$pi <- pi_y$pi[[1]]
      paramy0$gamma_i <- pi_y$gamma_i[[1]]

      theta_y <- draw_theta_y0_cpp(dataY, paramy0)
      paramy0$theta <- theta_y[[1]]

      tau2_y <- draw_tau2_y0_cpp(dataY, paramy0)
      paramy0$tau2 <- tau2_y[[1]]

      s_y <- draw_s_y0_cpp(dataY, paramy0)
      paramy0$s <- s_y[[1]]
    } else {
      gamma_i <- draw_gamma_y0_i_hs_cpp(dataY, paramy0)

      paramy0$gamma_i <- gamma_i$gamma_i
      paramy0$tau <- gamma_i$tau
      paramy0$lambda <- gamma_i$lambda
    }

    phi_f_y <- draw_phi_f_y0_j_cpp(dataY, paramy0)
    paramy0$phi_f <- phi_f_y[[1]]

    sigma2_y <- draw_sigma2_eps_y0_cpp(dataY, paramy0)
    paramy0$sigma2 <- sigma2_y[[1]]

    # # Step 2-2
    y0_mis <- draw_y0_mis_cpp(dataY, paramp0, paramy0)
    paramy0$y0_mis <- as.numeric(y0_mis$y0_mis[[1]])
    paramy0$eps <- as.numeric(y0_mis$eps[[1]])

    # # Step 3
    delta_y <- draw_y0_delta_cpp(dataY, paramp0, paramy0)
    paramy0$tte <- delta_y$tte
    paramy0$delta <- delta_y$delta

    if(estimate_phi_delta_y == 1) {
      phi_delta_y <- draw_phi_delta_y_cpp(dataY, paramy0, 0)
      paramy0$phi_delta <- as.numeric(phi_delta_y[[1]]);

      sigma2_eta_y <- draw_sigma2_eta_y_cpp(dataY, paramy0, 0)
      paramy0$sigma2_eta <- sigma2_eta_y[[1]]
    }
    
    ###### save MCMC results ######
      
    if (ng > NBURN & ng %% THIN == 0) {
      
      if(k_y1 > 0) {
        for(l in 1:k_y1) {
          MCMC_p_beta[[l]][(ng - NBURN)/THIN, ] <- t(paramp0[[l]]$beta)
          MCMC_p_alpha_i[[l]][,,(ng - NBURN)/THIN] <- paramp0[[l]]$alpha_i
          MCMC_p_xi[[l]][,,(ng - NBURN)/THIN] <- paramp0[[l]]$xi_t
          MCMC_p_f[[l]][,,(ng - NBURN)/THIN] <- paramp0[[l]]$f_p_t
          MCMC_p_gamma_i[[l]][,,(ng - NBURN)/THIN] <- paramp0[[l]]$gamma_i
          
          if (is.matrix(paramp0[[l]]$phi_xi)) {
            MCMC_p_phi_xi[[l]][(ng - NBURN)/THIN,] <- diag(paramp0[[l]]$phi_xi)
          } else {
            MCMC_p_phi_xi[[l]][(ng - NBURN)/THIN,] <- paramp0[[l]]$phi_xi
          }
          
          
          if (length(paramp0[[l]]$phi_f == 1)) paramp0[[l]]$phi_f <- as.matrix(paramp0[[l]]$phi_f)
          
          MCMC_p_phi_f[[l]][(ng - NBURN)/THIN,] <- diag(paramp0[[l]]$phi_f)
          MCMC_p_sigma2_e[[l]][(ng - NBURN)/THIN,] <- diag(paramp0[[l]]$sigma2e)
          MCMC_p_sigma2_eps[[l]][(ng - NBURN)/THIN] <- paramp0[[l]]$sigma2
          MCMC_p_pi[[l]][(ng - NBURN)/THIN, ] <- paramp0[[l]]$pi
          MCMC_p_theta[[l]][(ng - NBURN)/THIN] <- paramp0[[l]]$theta
          MCMC_p_tau2[[l]][(ng - NBURN)/THIN] <- paramp0[[l]]$tau2
          MCMC_p_s[[l]][(ng - NBURN)/THIN] <- paramp0[[l]]$s
          MCMC_p_mu_alpha[[l]][(ng - NBURN)/THIN,] <- paramp0[[l]]$mu_alpha
          MCMC_p_p0_mis[[l]][(ng - NBURN)/THIN, ] <- paramp0[[l]]$p0_mis
          MCMC_p_delta[[l]][(ng - NBURN)/THIN, ] <- paramp0[[l]]$delta
          
          if(estimate_phi_delta_p[l] == 1) {
            MCMC_p_phi_delta[[l]][(ng - NBURN)/THIN, ] <- paramp0[[l]]$phi_delta
            MCMC_p_sigma2_eta[[l]][(ng - NBURN)/THIN] <- paramp0[[l]]$sigma2_eta
          }
          
          MCMC_p_tau[[l]][(ng - NBURN)/THIN, ] <- paramp0[[l]]$tau
          MCMC_p_lambda[[l]][,,(ng - NBURN)/THIN] <- paramp0[[l]]$lambda
        }
      }
      
      MCMC_y_beta[(ng - NBURN)/THIN, ] <- t(paramy0$beta)
      MCMC_y_alpha_i[,,(ng - NBURN)/THIN] <- paramy0$alpha_i
      MCMC_y_xi[,,(ng - NBURN)/THIN] <- paramy0$xi_t
      MCMC_y_f[,,(ng - NBURN)/THIN] <- paramy0$f_t
      MCMC_y_gamma_i[,,(ng - NBURN)/THIN] <- paramy0$gamma_i
      
      if (is.matrix(paramy0$phi_xi)) {
        MCMC_y_phi_xi[(ng - NBURN)/THIN,] <- diag(paramy0$phi_xi)
      } else {
        MCMC_y_phi_xi[(ng - NBURN)/THIN,] <- paramy0$phi_xi
      }
      
      if (length(paramy0$phi_f == 1)) paramy0$phi_f <- as.matrix(paramy0$phi_f)
      
      MCMC_y_phi_f[(ng - NBURN)/THIN,] <- diag(paramy0$phi_f)
      MCMC_y_sigma2_e[(ng - NBURN)/THIN,] <- diag(paramy0$sigma2e)
      MCMC_y_sigma2_eps[(ng - NBURN)/THIN] <- paramy0$sigma2
      MCMC_y_pi[(ng - NBURN)/THIN, ] <- paramy0$pi
      MCMC_y_theta[(ng - NBURN)/THIN] <- paramy0$theta
      MCMC_y_tau2[(ng - NBURN)/THIN] <- paramy0$tau2
      MCMC_y_s[(ng - NBURN)/THIN] <- paramy0$s
      MCMC_y_mu_alpha[(ng - NBURN)/THIN,] <- paramy0$mu_alpha_i
      MCMC_y_y0_mis[(ng - NBURN)/THIN, ] <- paramy0$y0_mis
      MCMC_y_tte[(ng - NBURN)/THIN, ] <- paramy0$tte
      MCMC_y_delta[(ng - NBURN)/THIN, ] <- paramy0$delta
      MCMC_y_mte[(ng - NBURN)/THIN, ] <- paramy0$tte - paramy0$delta
      
      if(estimate_phi_delta_y == 1) {
       MCMC_y_phi_delta[(ng - NBURN)/THIN, ] <- paramy0$phi_delta
       MCMC_y_sigma2_eta[(ng - NBURN)/THIN] <- paramy0$sigma2_eta
      }

      MCMC_y_tau[(ng - NBURN)/THIN, ] <- paramy0$tau
      MCMC_y_lambda[,,(ng - NBURN)/THIN] <- paramy0$lambda
      
    }
  }
  
  ################## Saving Results and Return   ################## 
  
  if(k_y1 > 0) {
    MCMC_P <- list(beta = MCMC_p_beta, alpha_i = MCMC_p_alpha_i, xi = MCMC_p_xi, 
                   f = MCMC_p_f, gamma_i = MCMC_p_gamma_i, 
                   phi_f = MCMC_p_phi_f, sigma2_e = MCMC_p_sigma2_e, sigma2_eps = MCMC_p_sigma2_eps, 
                   mu_alpha = MCMC_p_mu_alpha, delta = MCMC_p_delta,
                   phi_delta = MCMC_p_phi_delta, sigma2_eta = MCMC_p_sigma2_eta,
                   p0_mis = MCMC_p_p0_mis, factor_selection_method = factor_selection_method_p,
                   pi = MCMC_p_pi, theta = MCMC_p_theta, tau2 = MCMC_p_tau2, s = MCMC_p_s, 
                   tau = MCMC_p_tau, lambda = MCMC_p_lambda)
  } else {
    MCMC_P <- NULL
  }
  
  MCMC_Y <- list(beta = MCMC_y_beta, alpha_i = MCMC_y_alpha_i, xi = MCMC_y_xi, 
                 f = MCMC_y_f, gamma_i = MCMC_y_gamma_i, 
                 phi_f = MCMC_y_phi_f, sigma2_e = MCMC_y_sigma2_e, sigma2_eps = MCMC_y_sigma2_eps, 
                 mu_alpha = MCMC_y_mu_alpha, y0_mis = MCMC_y_y0_mis, tte = MCMC_y_tte, 
                 delta = MCMC_y_delta, mte= MCMC_y_mte, 
                 phi_delta = MCMC_y_phi_delta, sigma2_eta = MCMC_y_sigma2_eta,
                 factor_selection_method = factor_selection_method_y,
                 pi = MCMC_y_pi, theta = MCMC_y_theta, tau2 = MCMC_y_tau2, s = MCMC_y_s, 
                 tau = MCMC_y_tau, lambda = MCMC_y_lambda)
  
  if(k_y1 > 0)  res_list = list(dataP = dataP, dataY = dataY, MCMC_P = MCMC_P, MCMC_Y = MCMC_Y) 
  else res_list = list(dataY = dataY, MCMC_Y = MCMC_Y) 
  
  return(res_list)
}
