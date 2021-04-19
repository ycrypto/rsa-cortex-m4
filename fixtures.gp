default(parisize,"64G")

\\ examples
e = 65537
pp256 = 0xf48922fe8e8cf7e238c32399aacd26d2467ec5510efb5113ad2bcc37e6fe2bed
p256 = 0xddbb94f11af83b2adf02e961bd5ad74aca27a8bd7ee8dd0cab998f987cd022f9
qq256 = 0xf146b14fe50dad906063caba3606e1157dee090be85c7cdb06022ea6dd306c63
q256 = 0xcd58cd8accf2db4c839d2553116bef81f0292b4e2d2b3f7df0e5dc8a0721398f
msg480 = 0x6a7f5d4a4ddff708442d837f7dc6ddb098bd44fd68854b691677e7665f81c4e4492f4e4200abf1a7b889006f30bc2fdc3743c94a647f78fe15293367

\\ p,q primes, c ciphertext
rsadp_crt(p, q, c) = {
  dp = lift(1/Mod(e, p - 1));
  dq = lift(1/Mod(e, q - 1));
  qinv = lift(1/Mod(q, p));
  n = p*q;
  mp = lift(Mod(c, p)^dp);
  mq = lift(Mod(c, q)^dq);
  h = lift(Mod((mp - mq)*qinv, p));
  m = lift(Mod(mq + q*h, n));

  return(m)
}

\\ m plaintext
rsaep(m) = {
  n = p*q;
  lift(Mod(m, n)^e)
}

p = pp256;
q = qq256;
c = msg480;

\\ watch out: GP/PARI does not have local variables
\\ with shadowing. doing this with "m = msg480" fails
e_then_d = rsaep(rsadp_crt(p, q, c)) == c;
d_then_e = rsadp_crt(p, q, rsaep(c)) == c;
