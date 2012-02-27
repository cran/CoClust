
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

## ***************************************************************************************************

setClass("CoClust",
         representation(Number.of.Clusters="integer"
                        ,Index.Matrix="matrix"
                        ,Data.Clusters="matrix"
                        ,Dependence = "list"
                        ,LogLik  = "numeric"
                        ,Est.Method = "character"
                        ,Opt.Method = "character"
                        ,BICk = "numeric"
                        ),
         prototype = list(Number.of.Clusters=integer()
                        ,Index.Matrix=matrix(0,0,0)
                        ,Data.Clusters=matrix(0,0,0)
                        ,Dependence = list(Param=NULL,Std.Err=NULL,P.value=NULL)
                        ,LogLik  = numeric()
                        ,Est.Method = character()
                        ,Opt.Method = character()
                        ,BICk = numeric()
                        )
         )
## ***************************************************************************************************


CoClust <- function(m, dimset = 2:5, nk = 12, copula = "frank", method.ma = c("empirical", "pseudo"), method.c = c("ml", "mpl", "irho", "itau"), dfree = NULL, writeout = 10, ...){
    #
    if(!is.numeric(writeout)|!writeout>0)
        stop("writeout should be a positive integer number");
    G <- nrow(m);
    if(nk>G)
        stop("nk should be <= than the nrow of entry data matrix");
    if(nk<max(dimset))
        stop("nk should be <= that the max(dimset)");
    if(length(dimset)<1 | max(dimset)>ncol(m))
        stop("dimset should be in 2 to ncol of entry data matrix");
    if(copula == "t" & is.null(dfree))
            warning("dfree should be specified only when the copula is a tcopula")
    #
    R       <- abs(cor(t(m),method="spearman"));
    R2      <- as.vector(as.dist(R));
    indici  <- matrix(rep(1:G,G),G);
    righe   <- as.vector(as.dist(indici));
    colonne <- as.vector(as.dist(t(indici)));
    o       <- order(R2, decreasing=TRUE);
    RV      <- cbind(righe[o], colonne[o], R2[o]); # vectorize R matrix; it containes row and col indexes
    # Steps 1. - 2.
    loglik         <- double();
    nk             <- nk;
    matrice.indici <- list();
    h              <- 0;
    permok         <- NULL;
    permok.k       <- list();
    for(k in dimset){
        RV2             <- RV
        noc             <- floor(nk/k)
        matrice.indici3 <- matrix(0, noc, (k+1), byrow=TRUE) # matrix with allocated k-plet indexes and the loglik of the copula fit (of the all allocated k-plets)
        i               <- 0;
        while(i<floor(noc)){
            i <- i+1
            # based on the max of the max of the Speraman's correlationa, it creates the k-plet candidates to the allocation
            if(is.vector(RV2)){
                start3 <- RV2[1:2];
            }else{
                start3 <- RV2[1,1:2];
            }
            if(k>=3 & is.vector(RV2)==FALSE){
                if(nrow(RV2)>=k){
                    RV2  <- RV2[-1,]
                    cand <- NULL
                    aa   <- NULL
                    for(j in 1:2){
                        aa <- which(RV2==start3[j],arr.ind=TRUE)
                        if(is.matrix(aa)){
                            candrow   <- aa[which.min(aa[,1]),1];
                            if(aa[which.min(aa[,1]),2]==2){
                                cand1 <- c(RV2[candrow,2],RV2[candrow,1],RV2[candrow,3]);
                            }else{
                                cand1 <- RV2[candrow,];
                            }
                        }else{
                            if(aa[2]==2){
                                cand1 <- c(RV2[aa,2],RV2[aa,1],RV2[aa,3]);
                            }else{
                                cand1 <- RV2[aa,];
                            }
                        }
                        cand <- rbind(cand,cand1);
                    }
                    start3   <- c(start3, cand[which.max(cand[,3]),2])
                    if(k>=4){
                        for(n in 4:k){
                            cand <- NULL
                            aa   <-NULL
                            p    <- 1:(n-1)
                            for(j in p){
                                pp <- setdiff(p,j)
                                cc <- which(RV2==start3[pp[1]],arr.ind=TRUE)[,1];
                                for(l in 2:length(pp)){
                                    cc <- c(cc,which(RV2==start3[pp[l]],arr.ind=TRUE)[,1]);
                                }
                                a <- RV2[-cc,]
                                if(is.vector(a)){
                                    if(which(a==start3[j])==2){
                                        cand1 <- c(a[2],a[1],a[3]);
                                    }else{
                                        cand1 <- a;
                                    }
                                }else{
                                    aa <- which(a==start3[j],arr.ind=TRUE);
                                    if(is.matrix(aa)){
                                        candrow   <- aa[which.min(aa[,1]),1];
                                        if(aa[which.min(aa[,1]),2]==2){
                                            cand1 <- c(a[candrow,2],a[candrow,1],a[candrow,3]);
                                        }else{
                                            cand1 <- a[candrow,];
                                        }
                                    }else{
                                        if(aa[2]==2){
                                            cand1 <- c(a[aa,2],a[aa,1],a[aa,3]);
                                        }else{
                                            cand1 <- a[aa,];
                                        }
                                    }
                                }
                                cand <- rbind(cand,cand1);
                            }
                            start3   <- c(start3, cand[which.max(cand[,3]),2]);
                        }
                    }
                }
            }
            if(length(start3)==k){
                matrice.indici3[i,1:k] <- start3
                perm                   <- CoClust_perm(m, mindex = matrice.indici3[1:i,], nmarg = k, copula = copula, method.ma, method.c, dfree)
                matrice.indici3[i,]    <- perm[[2]][i,];
                # rule for allocating or discarding the created k-pla
                if(i>1){
                    if(perm[[5]] < matrice.indici3[(i-1),(k+1)]){
                        matrice.indici3[i,] <- rep(0,(k+1))
                        perm                <- permok
                        i                   <- i-1;
                    }else{
                        permok <- perm;
                    }
                }else{
                    permok     <- perm;
                }
            }
            if(!is.null(dim(RV2)) & length(start3)==k){
                ind <- matrix(FALSE, nrow(RV2), 2)
                for (j in 1:k) {
                    dum <- RV2[, 1:2] == start3[j]
                    ind <- ind | dum;
                }
                ind2 <- which(!apply(ind, MARGIN = 1, FUN = any))
                if(length(ind2)>0){
                    RV2 <- RV2[ind2, ];
                }else{
                    matrice.indici3 <- matrice.indici3[1:length(which(matrice.indici3[,(k+1)]!=0)),]
                    i               <- floor(noc)+1;
                }
            }else{
                matrice.indici3 <- matrice.indici3[1:length(which(matrice.indici3[,(k+1)]!=0)),]
                i               <- floor(noc)+1;
            }
        }
        h <- h+1
        matrice.indici[[h]] <- matrice.indici3
        if(is.vector(matrice.indici[[h]])){
            loglik[h] <- -2*matrice.indici[[h]][(k+1)]+log(k*ncol(m));
        }else{
            nocfin    <- nrow(matrice.indici[[h]])
            loglik[h] <- -2*matrice.indici[[h]][nocfin,(k+1)]+log(k*nocfin*ncol(m));
        }
        permok.k[[h]] <- permok;
    }
    nmarg         <- dimset[which.min(loglik)];
    index.matrix1 <- matrice.indici[[which.min(loglik)]];
    cat("\r Number of clusters selected: ", nmarg, "\n");
    # Steps 3. - 4.
    RV2 <- RV;
    noc <- floor(G/nmarg);
    if(is.matrix(index.matrix1)){
        nr <- nrow(index.matrix1);
    }else{
        nr            <- 1
        index.matrix1 <- as.matrix(t(index.matrix1));
    }
    permok <- permok.k[[which.min(loglik)]];
    cat("\r Allocated observations: ", nr, "\n");
    if(noc>nr){
        index.matrix        <- matrix(0, noc, (nmarg+1), byrow=TRUE)
        index.matrix[1:nr,] <- index.matrix1
        ind                 <- matrix(FALSE, nrow(RV2), 2)
        for (j in 1:nmarg){
            for(i in 1:nr){
                dum <- RV2[, 1:2] == index.matrix1[i,j]
                ind <- ind | dum;
            }
        }
        ind2 <- which(!apply(ind, MARGIN = 1, FUN = any))
        if(length(ind2)>0){
            max.ind <- which.max(RV2[ind2, 3])
            buona   <- RV2[ind2[max.ind],1:2]
            RV2     <- RV2[ind2, ];
        }
        i <- 0
        while(i<=noc){
            i <- i+1
            if(is.null(dim(RV2))){
                start3 <- RV2[1:2];
            }else{
                start3 <- RV2[1,1:2];
            }
            if(nmarg>=3){
                RV2  <- RV2[-1,]
                cand <- NULL
                aa   <- NULL
                for(j in 1:2){
                    aa <- which(RV2==start3[j],arr.ind=TRUE)
                    if(is.matrix(aa)){
                        candrow   <- aa[which.min(aa[,1]),1];
                        if(aa[which.min(aa[,1]),2]==2){
                            cand1 <- c(RV2[candrow,2],RV2[candrow,1],RV2[candrow,3]);
                        }else{
                            cand1 <- RV2[candrow,];
                        }
                    }else{
                        if(aa[2]==2){
                            cand1 <- c(RV2[aa,2],RV2[aa,1],RV2[aa,3]);
                        }else{
                            cand1 <- RV2[aa,];
                        }
                    }
                    cand <- rbind(cand,cand1);
                }
                start3   <- c(start3, cand[which.max(cand[,3]),2])
                if(nmarg>=4){
                    for(n in 4:nmarg){
                        cand <- NULL
                        aa   <-NULL
                        p    <- 1:(n-1)
                        for(j in p){
                            pp <- setdiff(p,j)
                            cc <- which(RV2==start3[pp[1]],arr.ind=TRUE)[,1];
                            for(l in 2:length(pp)){
                                cc <- c(cc,which(RV2==start3[pp[l]],arr.ind=TRUE)[,1]);
                            }
                            a <- RV2[-cc,]
                            if(is.vector(a)){
                                if(which(a==start3[j])==2){
                                    cand1 <- c(a[2],a[1],a[3]);
                                }else{
                                    cand1 <- a;
                                }
                            }else{
                                aa <- which(a==start3[j],arr.ind=TRUE);
                                if(is.matrix(aa)){
                                    candrow   <- aa[which.min(aa[,1]),1];
                                    if(aa[which.min(aa[,1]),2]==2){
                                        cand1 <- c(a[candrow,2],a[candrow,1],a[candrow,3]);
                                    }else{
                                        cand1 <- a[candrow,];
                                    }
                                }else{
                                    if(aa[2]==2){
                                        cand1 <- c(a[aa,2],a[aa,1],a[aa,3]);
                                    }else{
                                        cand1 <- a[aa,];
                                    }
                                }
                            }
                            cand <- rbind(cand,cand1);
                        }
                        start3 <- c(start3, cand[which.max(cand[,3]),2]);
                    }
                }
            }
            if(length(start3)==nmarg){
                index.matrix[(nr+i),1:nmarg] <- start3
                perm                         <- CoClust_perm(m, mindex = index.matrix[1:(nr+i),], nmarg = nmarg, copula = copula, method.ma, method.c,dfree)
                index.matrix[(nr+i),]        <- perm[[2]][(nr+i),];
                if(perm[[5]] < index.matrix[(nr+i-1),(nmarg+1)]){
                    index.matrix[(nr+i), ] <- rep(0, (nmarg+1))
                    perm                   <- permok
                    i                      <- i-1;
                }else{
                    permok <- perm;
                    if((nr+i)%%writeout==0) cat("\r Allocated observations: ", (nr+i), "\n");
                }
            }else{
                permok     <- perm;
                if((nr+i)%%writeout==0) cat("\r Allocated observations: ", (nr+i), "\n");
            }
            if(!is.null(dim(RV2)) & length(start3)==nmarg){
                ind <- matrix(FALSE, nrow(RV2), 2)
                for(j in 1:nmarg){
                    dum <- RV2[, 1:2] == start3[j]
                    ind <- ind | dum;
                }
                ind2 <- which(!apply(ind, MARGIN = 1, FUN = any))
                if(length(ind2)>0){
                    RV2 <- RV2[ind2, ]
                    if(is.vector(RV2) & nmarg!=2){
                        index.matrix <- index.matrix[1:length(which(index.matrix[,(nmarg+1)]!=0)),]
                        i            <- floor(noc)+1;
                    }
                }else{
                    index.matrix <- index.matrix[1:length(which(index.matrix[,(nmarg+1)]!=0)),]
                    i            <- floor(noc)+1;
                }
            }else{
                index.matrix <- index.matrix[1:length(which(index.matrix[,(nmarg+1)]!=0)),]
                i            <- floor(noc)+1;
            }
        }
    }
    fin <- permok;
    #
    colnames(fin[[2]]) <- c(paste("Cluster",1:nmarg),"LogLik");
    names(loglik)      <- dimset;
    #
    if(inherits(fin,"try-error")){
         cat("Clustering failed")
         return(simpleError("Clustering Failed", call = NULL));
     }else{
        out <- new("CoClust")
        out@Number.of.Clusters <- fin[[1]];
        out@Index.Matrix       <- fin[[2]];
        out@Data.Clusters      <- fin[[3]];
        out@Dependence         <- fin[[4]];
        out@LogLik             <- fin[[5]];
        out@Est.Method         <- fin[[6]];
        out@Opt.Method         <- fin[[7]];
        out@BICk               <- loglik;
        return(out);
    }
}
