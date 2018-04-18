with(ListTools):
with(combinat):
with(Physics):
with(Threads):
with(GroupTheory):
interface(labelling=false):

Setup(mathematicalnotation=true, anticommutativecolor=olive):
Setup(anticommutativeprefix={phi,theta,tau,eta,psi,rho}):


#Protecting variable names to avoid non-omniscient program user errors.
protect(a);
protect(m);
protect(n);
protect(p);
protect(h);
protect(e);
protect(s);
protect(sbar);
protect(sEt);
protect(sbarEt);
protect(beta);
protect(alpha);
protect(box):
protect(circle):


read "./lib/sparts.mpl";
read "./lib/types.mpl";
read "./lib/operators.mpl";
read "./lib/basis.mpl";
read "./lib/CMS.mpl";
read "./lib/visual.mpl";
read "./lib/sBern_1.mpl";
read "./lib/bernsteinLAV.mpl";
####################################################################################################
#interface(screenwidth=100);
