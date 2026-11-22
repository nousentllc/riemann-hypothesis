\\ Run with gp -q -f certify_fields.gp. The calling driver checks the full transcript.
fixedclasses(b)=
{
  my(pol=b.pol,aut=nfgaloisconj(b),cyc=b.cyc,r=#cyc,out=List());
  for(i=1,#aut,
    my(s=aut[i]);
    if(Mod(s,pol)==Mod(x,pol) || Mod(subst(subst(s,x,s),x,s),pol)!=Mod(x,pol),next);
    my(cols=vector(r,j,bnfisprincipal(b,nfgaloisapply(b,s,b.gen[j]),0)));
    my(M=matrix(r,r,j,k,cols[k][j]),count=0);
    forvec(v=vector(r,j,[0,cyc[j]-1]),
      my(d=(M-matid(r))*v~);
      if(vector(r,j,d[j]%cyc[j])==vector(r),count++);
    );
    listput(out,count);
  );
  if(#out!=2 || out[1]!=out[2] || out[1]%3!=b.no%3,error("Unexpected order-three action"));
  return(Vec(out));
};
cert(label, pol, withaction=0)=
{
  my(b=bnfinit(pol,1),cl=b.cyc,h=b.no,ok=bnfcertify(b));
  if(ok!=1,error("Full certification failed"));
  print([label,poldegree(pol),b.disc,h,cl,ok,Vec(pol),if(withaction,fixedclasses(b),[])]);
};
print(["pari",version()]);
for(n=1,3,cert(Str("cyclotomic_",3^n),polcyclo(3^n)));
{
  my(ps=polsubcyclo(91,3),k=0);
  for(i=1,#ps,
    if(nfdisc(ps[i])==91^2,
      k++;
      cert(Str("diagonal_cubic_",k),ps[i]);
      cert(Str("diagonal_over_zeta3_",k),polredabs(polcompositum(polcyclo(3),ps[i])[1]),1);
    );
  );
  if(k!=2,error("Expected two conductor-91 subfields"));
}
quit()
