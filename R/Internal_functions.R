
### CoClust
### A COPULA BASED CLUSTERING ALGORITHM
##
##  The authors of this software are
##  Francesca Marta Lilja Di Lascio, and
##  Simone Giannerini, Copyright (c) 2012

##  Permission to use, copy, modify, and distribute this software for any
##  purpose without fee is hereby granted, provided that this entire notice
##  is included in all copies of any software which is or includes a copy
##  or modification of this software and in all copies of the supporting
##  documentation for such software.
##
##  This program is free software; you can redistribute it and/or modify
##  it under the terms of the GNU General Public License as published by
##  the Free Software Foundation; either version 2 of the License, or
##  (at your option) any later version.
##
##  This program is distributed in the hope that it will be useful,
##  but WITHOUT ANY WARRANTY; without even the implied warranty of
##  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
##  GNU General Public License for more details.
##
##  A copy of the GNU General Public License is available at
##  http://www.r-project.org/Licenses/

## **************************************************************************************************

fit.margin <- function(dataset, param=list(dimc=NULL)){
    dimc <- param$dimc
    udath <- matrix(0, nrow=ncol(dataset), ncol=dimc)
    ecdfc <- function(x){
        #  MODIFIED VERSION OF THE FUNCTION ecdf WITH DENOMINATOR N+1
        x <- sort(x)
        n <- length(x)
        if (n < 1)
            stop("'x' must have 1 or more non-missing values")
        vals <- sort(unique(x))
        rval <- approxfun(vals, cumsum(tabulate(match(x, vals)))/(n+1), method = "constant", yleft = 0, yright = 1, f =
        0, ties = "ordered")
        class(rval) <- c("ecdf", "stepfun", class(rval))
        attr(rval, "call") <- sys.call()
        rval
    }
    for(k in 1:dimc){
        empir <- ecdfc(dataset[k,])
        udath[,k]  <- empir(dataset[k,])
    }
    return(udath)
}
## **************************************************************************************************

fit.margin2 <- function(dataset, param = list(dimc = NULL)) {
    n <- ncol(dataset)
    udath <- apply(t(dataset), 2, rank)/(n + 1)
    return(udath)
}

## **************************************************************************************************

fit.margin3 <- function(dataset, param = list(fn, gr = NULL, y = NULL, control, dimc = NULL)) {
    fn <- param$fn
    gr <- param$gr
    y  <- param$y
    control <- param$control
    dimc <- param$dimc
    bh <- matrix(0, dimc, 2)
    udath <- matrix(0, dim(dataset)[2], dimc)
    for (k in 1:dimc) {
        bh[k, ] <- optim(par = c(mean(dataset[k, ]),
          sd(dataset[k, ])), fn = fn, gr = gr, control = control,
          y = y[k, ])$par
        udath[, k] <- pnorm(dataset[k, ], bh[k, 1], bh[k,
          2])
    }
    return(udath)
}
## **************************************************************************************************

stima_cop <- function (m, nmarg = 3, copula = "frank", method.ma = c("empirical", "pseudo"), method.c = c("ml", "mpl", "irho", "itau"), dfree, ...){
    # m ha i margini (variabili) in riga e le obs in colonna
    method.ma <- match.arg(method.ma)
    n.row <- dim(m)[1]
    n.col <- dim(m)[2]
    if(copula %in% c("frank","clayton","gumbel")){
        metodo.opt0 <- c("BFGS", "Brent", "CG", "L-BFGS-B", "SANN")
    }else{
        metodo.opt0 <- c("BFGS", "Nelder-Mead", "CG", "L-BFGS-B", "SANN")
    }
    metodo.opt    <- setdiff(metodo.opt0, "BFGS")
    nmetopt0   <- length(metodo.opt0)
    nmetopt   <- length(metodo.opt)
    #
    metodo0    <- c("ml", "mpl", "irho", "itau")
    metodo    <- setdiff(metodo0, method.c)
    nmetstima0 <- length(metodo0)
    nmetstima <- length(metodo)
    #
    ifelse(n.row <= nmarg, dimc <- n.row, dimc <- nmarg)
    if (copula == "normal") {
        copulah <- normalCopula(0.5, dim = nmarg, dispstr = "ex")
        startco <- 0.5
    }else
    if (copula == "t") {
        copulah <- tCopula(0.5, dim = nmarg, dispstr = "ex", df=dfree)
        startco <- c(0.5, dfree)
    }else
    if (copula == "frank") {
        copulah <- frankCopula(21, dim = nmarg)
        startco <- 21
    }else
    if (copula == "clayton") {
        copulah <- claytonCopula(21, dim = nmarg)
        startco <- 21
    }else
    if (copula == "gumbel") {
        copulah <- gumbelCopula(21, dim = nmarg)
        startco <- 21
    }
    n.marg <- nmarg
    dum <- m
    if (method.ma == "empirical") {
        param <- list(dimc = n.marg)
        udat <- fit.margin(dataset = dum, param = param)
    }else if (method.ma == "pseudo") {
            udat <- fit.margin2(dataset=dum)
    }
    fitfin <- try(fitCopula(data = udat, copula = copulah, start = startco, method = method.c), silent = TRUE)
    if((inherits(fitfin, "try-error")!=TRUE)) LL <- suppressWarnings(loglikCopula(fitfin@estimate, udat, copulah))
    metodo.fin <- method.c
    h <- 0
    while(((inherits(fitfin, "try-error")==TRUE) || !is.finite(LL)) & h<nmetstima){
        h <- h+1
        metodo.c <- metodo[h]
        if(metodo.c=="ml"){
            param <- list(dimc = n.marg)
            udat <- fit.margin(dataset=dum, param=param)
        }else{
            udat <- fit.margin2(dataset=dum)
        }
        fitfin <- try(fitCopula(data = udat, copula = copulah,
            start = startco, method = metodo.c), silent = TRUE)
        if((inherits(fitfin, "try-error")!=TRUE)){
            if(fitfin@estimate<=0) fitfin@estimate <- 0.000000001
            LL <- suppressWarnings(loglikCopula(fitfin@estimate, udat, copulah))
            metodo.fin <- metodo.c
        }
    }
    hm <- 0
    while(((inherits(fitfin, "try-error")==TRUE) || !is.finite(LL)) & hm<nmetstima0){
        hm <- hm+1
        metodo.c <- metodo0[hm]
        if(metodo.c=="ml"){
            param <- list(dimc = n.marg)
            udat <- fit.margin(dataset=dum, param=param)
        }else{
            udat <- fit.margin2(dataset=dum)
        }
        h <- 1
        fitfin <- try(fitCopula(data = udat, copula = copulah,
                start = startco, method = metodo.c, optim.method=metodo.opt[h]), silent = TRUE)
        if((inherits(fitfin, "try-error")!=TRUE)){
            if(fitfin@estimate<=0) fitfin@estimate <- 0.000000001
            LL <- suppressWarnings(loglikCopula(fitfin@estimate, udat, copulah))
            metodo.fin <- metodo.opt[h]
        }
        while(((inherits(fitfin, "try-error")==TRUE)||!is.finite(LL)) & h<nmetopt){
            h <- h+1
            fitfin <- try(fitCopula(data = udat, copula = copulah,
                        start = startco, method = metodo.c, optim.method=metodo.opt[h]), silent = TRUE)
            if((inherits(fitfin, "try-error")!=TRUE)){
                if(fitfin@estimate<=0) fitfin@estimate <- 0.000000001
                LL <- suppressWarnings(loglikCopula(fitfin@estimate, udat, copulah))
                metodo.fin <- metodo.opt[h]
            }
        }
    }
    if(((inherits(fitfin, "try-error")==TRUE) || !is.finite(LL))) {
        class(fitfin) <- "try-error"
        return(fitfin)
    }else {
        list(
        Param <- fitfin@estimate,
        se <- as.numeric(sqrt(fitfin@var.est)),
        zvalue <- Param/se,
        pvalue <- as.numeric((1 - pnorm(abs(zvalue))) * 2),
        LogLik <- LL,
        Estimation.Method <- fitfin@method,
        Optim.Method <- metodo.fin
        )
    }
}
## **************************************************************************************************

CoClust_perm <- function (m, mindex, nmarg = 3, copula = "frank", method.ma = c("empirical", "pseudo"), method.c = c("ml", "mpl", "irho", "itau"), dfree, ...){
    # mindex: matrice indici di riga con le loglik fino a quella di posto (nrow(mindex)-1)
    # m: geni in riga
    n.col <- dim(m)[2]
    #
    if(is.vector(mindex) || nrow(mindex)==1){
        fitfin <- stima_cop(m[mindex[1:nmarg],], nmarg = nmarg, copula = copula, method.ma, method.c,dfree)
        if(class(fitfin)!="try-error"){
            result <- matrix(c(mindex[1:nmarg], fitfin[[5]]),nrow=1,byrow=TRUE)
            mfin <- t(m[mindex[1:nmarg],])
        }
    }else{
        noc <- nrow(mindex)
        result <- matrix(0, nrow = noc, ncol = (nmarg + 1))
        result[1:(noc-1), ] <- mindex[1:(noc-1),]
        dum <- matrix(0, (noc*n.col), nmarg)
        mfin <- matrix(0, (noc*n.col), nmarg)
        mfin[1:((noc-1)*n.col), 1:nmarg] <- t(m[mindex[1:(noc-1),1:nmarg],]) # obs in row e margini/var in cols
        buona <- mindex[noc,1:nmarg]
        if(length(buona)>=nmarg){
            combinat <- permutations(nmarg, nmarg, buona)
            ntry <- dim(combinat)[1]
            logl <- double(length = ntry)
            for (j in 1:ntry) {
                dum <- cbind(t(mfin[(1:(n.col*(noc-1))), ]), m[combinat[j, ], ])
                    # dum ha i geni in riga
                fitc <- stima_cop(dum, nmarg = nmarg, copula = copula, method.ma, method.c,dfree)
                if(inherits(fitc, "try-error")){
                    logl[j] <- -.Machine$double.xmax
                }else{
                    logl[j] <- fitc[[5]]
                }
            } # end ntry
            ## TODO fare un while su res3 in modo tale che se fitfin della k-pla selezionata dà errore allora sceglie le altre permutazioni
            res3 <- cbind(combinat, logl)
            result[noc,1:nmarg] <- res3[which.max(logl),1:nmarg]
            mfin[((noc-1)*n.col + 1):(noc*n.col), ] <- t(m[result[noc, 1:nmarg], ])
        } # end if su length(buona)
        nam <- vector(length = nmarg)
        dum <- t(mfin)
        for (j in 1:nmarg) {
            nam[j] <- paste("Cluster", j, sep = "")
            colnames(mfin) <- nam
        }
        fitfin <- stima_cop(dum, nmarg = nmarg, copula = copula, method.ma, method.c, dfree)
        if(class(fitfin)!="try-error"){
            result[noc, nmarg+1] <- fitfin[[5]]
        }
    }
    if(class(fitfin)=="try-error"){
        return(fitfin)
    }else{
        Param  <- fitfin[[1]]
        se     <- fitfin[[2]]
        zvalue <- Param/se
        pvalue <- as.numeric((1 - pnorm(abs(zvalue))) * 2)
        depfin <- list(Param = Param, Std.Err = se, P.value = pvalue)
        return(list(
        Number.of.Clusters <- as.integer(nmarg),
        Index.Matrix <- result,
        Data.Clusters <- mfin,
        Dependence <- depfin ,
        LogLik <- fitfin[[5]],
        Estimation.Method <- fitfin[[6]],
        Optim.Method <- fitfin[[7]]
        ))
    }
}
## **************************************************************************************************
