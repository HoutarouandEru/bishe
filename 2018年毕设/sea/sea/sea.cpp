
#include <iostream>
#include <iomanip>
#include <fstream>
#include <cstring>
#include "ecn.h"         // Elliptic Curve Class
#include "crt.h"         // Chinese Remainder Theorem Class
#pragma comment(lib,"miracl.lib")
//
// poly.h implements polynomial arithmetic. FFT methods are used for maximum
// speed, as the polynomials can get very big. 
// But all that gruesome detail is hidden away.
//
// polymod.h implements polynomial arithmetic wrt to a preset poynomial 
// modulus. This looks a bit neater. Function setmod() sets the modulus 
// to be used. Again fast FFT methods are used.
//
// polyxy.h implements a bivariate polynomial class
//

#include "poly.h"
#include "polymod.h"
#include "polyxy.h"

using namespace std;

#ifndef MR_NOFULLWIDTH
Miracl precision=18;            // max. 18x32 bits per big number
#else
Miracl precision(18,MAXBASE); 
#endif

PolyMod MY2,MY4;

ZZn A,B;         // Here ZZn are integers mod the prime p
                 // Montgomery representation is used internally

BOOL Edwards=FALSE;

// Elliptic curve Point duplication formula

void elliptic_dup(PolyMod& X,PolyMod& Y,PolyMod& Z)
{ // (X,Y,Z)=2.(X,Y,Z)
    PolyMod W1,W2,W3,W4;

    W2=Z*Z;           // 1
    W3=A*(W2*W2);     // 2
    W1=X*X;           // 3
    W4=3*W1+W3;
    Z*=(2*Y);          // 4   Z has an implied y
    W2=MY2*(Y*Y);     // 5
    W3=4*X*W2;        // 6
    W1=W4*W4;         // 7
    X=W1-2*W3;
    W2*=W2;
    W2*=8;     // 8
    W3-=X;
    W3*=W4;         // 9  polynomial multiplications
    Y=W3-W2;    
    X*=MY2;          // fix up - move implied y from Z to Y
    Y*=MY2;
    Z*=MY2;
}

void elliptic_add(PolyMod& XT,PolyMod& YT,PolyMod& ZT,PolyMod& X,PolyMod& Y)
{ // add (X,Y,1) to (XT,YT,ZT)
  // on an elliptic curve 
    PolyMod W1,W2,W4,W5,W6;

    W1=XT;
    W6=ZT*ZT;       // 1
    W4=X*W6;        // 2  * 
    W1-=W4;

    W2=YT;          // W2 has an implied y
    W6*=ZT;         // 3
    W5=Y*W6;        // 4  * W5 has an implied y 
    W2-=W5;
    if (iszero(W1))
    {
        if (iszero(W2)) 
        { // should have doubled
            elliptic_dup(XT,YT,ZT);
             return;
        }
        else
        { // point at infinity
            ZT.clear();
            return;    
        }
    }

    W4=W1+2*W4;     // W4=2*W4+W1 
    W5=W2+2*W5;     // W5=2*W5+W2

    ZT*=W1;       // 5

    W6=W1*W1;       // 6
    W1*=W6;         // 7
    W6*=W4;         // 8
    W4=MY2*(W2*W2);   // 9 Substitute for Y^2

    XT=W4-W6;

    W6=W6-2*XT;
    W2*=W6;       // 10
    W1*=W5;       // 11  polynomial multiplications
    W5=W2-W1;

    YT=W5/(ZZn)2;   

    return;
}

#define STORE 80
#define HERD 5

ECn wild[STORE],tame[STORE];
Big wdist[STORE],tdist[STORE];
int wname[STORE],tname[STORE];

Big kangaroo(Big p,Big order,Big ordermod)
{
    ECn ZERO,K[2*HERD],TE[2*HERD],X,P,G,table[128],trap;
    Big start[2*HERD],txc,wxc,mean,leaps,upper,lower,middle,a,b,x,y,n,w,t,nrp;
    int i,jj,j,m,sp,nw,nt,cw,ct,k,distinguished,nbits;
    Big D[2*HERD],s,distance[128],real_order;
    BOOL bad,collision,abort;
    forever
    {
// find a random point on the curve
        do
        {
            x=rand(p);
        } while (!P.set(x,x));

        lower=p+1-2*sqrt(p)-3; // lower limit of search
        upper=p+1+2*sqrt(p)+3; // upper limit of search

        w=1+(upper-lower)/ordermod;
        leaps=sqrt(w);
        mean=HERD*leaps/2;      // ideal mean for set S=1/2*w^(0.5)
        nbits=bits(leaps/16);
        if (nbits>30) nbits=30;
        distinguished=1<<nbits;
        for (s=1,m=1;;m++)
        { /* find table size */
            distance[m-1]=s*ordermod;
            s*=2;
            if ((2*s/m)>mean) break;
        }
        table[0]=ordermod*P;
        for (i=1;i<m;i++)
        { // double last entry
            table[i]=table[i-1];
            table[i]+=table[i-1];
        }

        middle=(upper+lower)/2;
        if (ordermod>1)
            middle+=(ordermod+order-middle%ordermod);  // middle must be
                                                       // order mod ordermod

        for (i=0;i<HERD;i++) start[i]=middle+13*ordermod*i; // tame ones
        for (i=0;i<HERD;i++) start[HERD+i]=13*ordermod*i;   // wild ones

        for (i=0;i<2*HERD;i++) 
        {
            K[i]=start[i]*P;         // on your marks ....
            D[i]=0;                  // distance counter
        }
        cout << "Releasing " << HERD << " Tame and " << HERD << " Wild Kangaroos\n";

        nt=0; nw=0; cw=0; ct=0;
        collision=FALSE;  abort=FALSE;
        forever
        { 
            for (jj=0;jj<HERD;jj++)
            {
                K[jj].get(txc);
                i=txc%m;  /* random function */

                if (txc%distinguished==0)
                {
                    if (nt>=STORE)
                    {
                        abort=TRUE;
                        break;
                    }
                    cout << "." << flush;
                    tame[nt]=K[jj];
                    tdist[nt]=D[jj];
                    tname[nt]=jj;
                    for (k=0;k<nw;k++)
                    {
                        if (wild[k]==tame[nt])
                        {
                            ct=nt; cw=k;
                            collision=TRUE;
                            break;
                        }
                    }
                    if (collision) break;
                    nt++;
                }
                D[jj]+=distance[i];
                TE[jj]=table[i];
            }
            if (collision || abort) break;
            for (jj=HERD;jj<2*HERD;jj++)
            {
                K[jj].get(wxc);
                j=wxc%m;

                if (wxc%distinguished==0)
                {
                    if (nw>=STORE)
                    {
                        abort=TRUE;
                        break;
                    }
                    cout << "." << flush;
                    wild[nw]=K[jj];
                    wdist[nw]=D[jj];
                    wname[nw]=jj;
                    for (k=0;k<nt;k++)
                    {
                        if (tame[k]==wild[nw]) 
                        {
                            ct=k; cw=nw;
                            collision=TRUE;
                            break;
                        }
                    }
                    if (collision) break;
                    nw++;
                }
                D[jj]+=distance[j];
                TE[jj]=table[j];
            }
            if (collision || abort) break;

            multi_add(2*HERD,TE,K);   // jump together - its faster
        }
        cout << endl;
        if (abort)
        {
            cout << "Failed - this should be rare! - trying again" << endl;
            continue;
        }
        nrp=start[tname[ct]]-start[wname[cw]]+tdist[ct]-wdist[cw]; 
                                                   // = order mod ordermod
        G=P;
        G*=nrp;
        if (G!=ZERO)
        {
            cout << "Sanity Check Failed. Please report to mike@compapp.dcu.ie" << endl;
            exit(0);
        }
        if (Edwards)
		{
			if (prime(nrp/4))
			{
				cout << "NP/4= " << nrp/4 << endl;
				cout << "NP/4 is Prime!" << endl;
				break;
			}
		}
		else
		{
			if (prime(nrp))
			{
				cout << "NP= " << nrp << endl;
				cout << "NP is Prime!" << endl;
				break;
			}
		}

// final checks....
        real_order=nrp; i=0; 
        forever
        {
            sp=get_mip()->PRIMES[i];
            if (sp==0) break;
            if (real_order%sp==0)
            {
                G=P;
                G*=(real_order/sp);
                if (G==ZERO) 
                {
                    real_order/=sp;
                    continue;
                }
            }
            i++;
        }   
        if (real_order <= 4*sqrt(p))
        { 
            cout << "Low Order point used - trying again" << endl;
            continue;
        }
        real_order=nrp;
        for (i=0;(sp=get_mip()->PRIMES[i])!=0;i++)
            while (real_order%sp==0) real_order/=sp;
        if (real_order==1)
        { // all factors of nrp were considered
            cout << "NP= " << nrp << endl;
            break;
        }
        if (prime(real_order))
        { // all factors of NP except for one last one....
            G=P;
            G*=(nrp/real_order);
            if (G==ZERO) 
            {
                cout << "Failed - trying again" << endl;
                continue;
            }
            else 
            {
                cout << "NP= " << nrp << endl;
                break;
            }
        }

        bad=FALSE;
        for (i=0;i<10;i++)
        { 
            do
            {
                x=rand(p);
            } while (!P.set(x,x));
            G=P;
            G*=nrp;
            if (G!=ZERO)
            {
                bad=TRUE;
                break;
            }
        }
        if (bad)
        {
            cout << "Failed - trying again" << endl;
            continue;                       
        }
        cout << "NP is composite and not ideal for Cryptographic use" << endl;
        cout << "NP= " << nrp << " (probably)" << endl;
        break;
    }
    return nrp;
}


void get_ck(int terms,ZZn a,ZZn b,ZZn *c)
{
    int k,h;
    if (terms==0) return;
    c[1]=-a/5;
    if (terms==1) return;
    c[2]=-b/7;
    for (k=3;k<=terms;k++)
    {
        c[k]=0;
        for (h=1;h<=k-2;h++) c[k]+=c[h]*c[k-1-h];
        c[k]*=((ZZn)3/(ZZn)((k-2)*(2*k+3)));
    }
}


void mulquad(int p,int qnr,int x,int y,int& a,int& b)
{
    int olda=a;
    a=(a*x+b*y*qnr)%p;
    b=(olda*y+b*x)%p;     
}

void powquad(int p,int qnr,int x,int y,int e,int& a,int& b)
{
    int k=e;
    a=1;
    b=0;
    if (k==0) return;

    for(;;)
    {
        if (k%2!=0)
            mulquad(p,qnr,x,y,a,b);        
        k/=2;
        if (k==0) return;
        mulquad(p,qnr,x,y,x,y);
    }
}


int phi(int n)
{
    int i,r=1;
    for (i=2;i<n;i++) if (igcd(i,n)==1) r++;
    return r;
}

int main(int argc,char **argv)
{
    ofstream ofile;
    ifstream mueller;
    int SCHP,first,max,lower,ip,parity,pbits,lp,i,jj,is,n,nx,ny,nl;
    int sl[8],k,tau,lambda;
    mr_utype good[100],l[100],t[100];
    Big a,b,c,p,nrp,x,y,d,accum;
    PolyMod XX,YY,XP,XPP,YP,YPP;
    PolyXY MP,Gl[200];
    termXY *posXY;
    Poly F,G,P[500],P2[500],P3[500],Y2,Y4;
    miracl *mip=&precision;
    BOOL escape,search,fout,gotI,gotA,gotB,atkin;
    ZZn j,g,qb,qc,delta,el;
    ZZn EB,EA,T,T1,T3,A2,A4,AZ,AW;
    int Base; 

    argv++; argc--;
    if (argc<1)
    {
        cout << "Incorrect Usage" << endl;
        return 0;
    }

    ip=0;
    gprime(10000);                 // generate small primes < 1000
    search=fout=gotI=gotA=gotB=atkin=FALSE;
    a=0; b=0;

// Interpret command line
    Base=10;
    while (ip<argc)
    {
        if (!fout && strcmp(argv[ip],"-o")==0)
        {
            ip++;
            if (ip<argc)
            {
                fout=TRUE;
                ofile.open(argv[ip++]);
                continue;
            }
            else
            {
                cout << "Error in command line" << endl;
                return 0;
            }
        }
        if (!gotI && strcmp(argv[ip],"-i")==0)
        {
            ip++;
            if (ip<argc)
            {
                gotI=TRUE;

                mueller.open(argv[ip],ios::in);
                if (!mueller)
                {
                    cout << "input file " << argv[ip] << " could not be opened" << endl;
                    return 0;
                }
                ip++;
                continue;
            }
            else
            {
                cout << "Error in command line" << endl;
                return 0;
            }
        }

        if (strcmp(argv[ip],"-s")==0)
        {
            ip++;
            search=TRUE;
            continue;
        }

        if (strcmp(argv[ip],"-a")==0)
        {
            ip++;
            atkin=TRUE;
            continue;
        }

        if (strcmp(argv[ip],"-h")==0)
        {
            ip++;
            Base=16;
            continue;
        }

        if (strcmp(argv[ip],"-E")==0)
        {
            ip++;
            Edwards=TRUE;
            continue;
        }

        if (!gotA) 
        {
            mip->IOBASE=Base;
            a=argv[ip++];
            mip->IOBASE=10;
            gotA=TRUE;
            continue;
        }
        if (!gotB) 
        {
            mip->IOBASE=Base;
            b=argv[ip++];
            mip->IOBASE=10;
            gotB=TRUE;
            continue;
        }
        cout << "Error in command line" << endl;
        return 0;
    }    

    if (!gotI || !gotA || !gotB)
    {
        cout << "Error in command line" << endl;
        return 0;
    }

// get prime modulus from .pol file

    mueller >> p;
    pbits=bits(p);
    if (pbits<64)
    {
        cout << "Prime modulus too small for this program!" << endl;
        exit(0);
    }
    cout << "P= " << p << endl;
    cout << "P mod 24 = " << p%24 << endl;
    cout << "P is " << pbits << " bits long" << endl;
    cout << "Reading in pre-processed Modular Polynomials... " << endl;
//
// read in all pre-processed bivariate modular polynomials
//
    modulo(p);   // set modulus
    l[0]=2;
    max=0;
    for (i=1;;i++)
    {
        mueller >> lp;
        if (mueller.eof()) break;
        max=i;
        l[i]=lp;
        cout << setw(3) << lp << flush;
        posXY=NULL;
        Gl[i].clear();
        forever 
        {
            mueller >> c >> nx >> ny;
            posXY=Gl[i].addterm((ZZn)c,nx,ny,posXY);
            if (nx==0 && ny==0) break;
        }
        cout << "\b\b\b" << flush;
    }

    mueller.close();

// loop for "-s" search option

    forever {

    fft_reset();   // reset FFT tables

	if (Edwards)
	{
		modulo(p);
		EB=b;
		EA=a;
		AZ=(ZZn)1/(EA-EB);
		A2=2*(EA+EB)/(EA-EB);
		A4=1; AW=1;

		AW*=AZ; A2*=AZ; A4*=AZ;

		A4*=AW;

		T=4*A2;
		T1=3*T;
		T3=18*36*(2*A4);

		A=T3-3*T1*T1;
		B=-T1*T3+2*T1*T1*T1;
		ecurve((Big)A,(Big)B,p,MR_AFFINE);    // initialise Elliptic Curve

	}
	else
	{
		ecurve(a,b,p,MR_AFFINE);    // initialise Elliptic Curve
		A=a;
		B=b;
	}

// The elliptic curve as a Polynomial

    Y2=0;
    Y2.addterm(B,0);
    Y2.addterm(A,1);
    Y2.addterm((ZZn)1,3);
    Y4=Y2*Y2;

    cout << "Counting the number of points (NP) on the curve" << endl;
	if (Edwards)
	{
		cout << "X^2+" << EA << "*Y^2=X^2*Y^2+" << EB << endl;
		cout << "Equivalent to Weierstrass form" << endl;
	}
    cout << "y^2= " << Y2 << " mod " << p << endl;   

    delta=-16*(4*A*A*A+27*B*B);

    if (delta==0)
    {
        cout << "Not Allowed! 4A^3+27B^2 = 0" << endl;
        if (search) {b+=1; continue; }
        else return 0;
    }
    
 // Calculate j-invariant

    j=(-1728*64*A*A*A)/delta;

    if (j==0 || j==1728)
    {
        cout << "Not Allowed! j-invariant = 0 or 1728" << endl;
        if (search) {b+=1; continue; }
        else return 0;
    }


// Finding the order modulo 2
// If GCD(X^P-X,X^3+AX+B) == 1 , trace=1 mod 2, else trace=0 mod 2

    XX=0;
    XX.addterm((ZZn)1,1);
    YY=0;
    YY.addterm((ZZn)-1,0);      // Point (X,-Y)
    setmod(Y2);

    XP=pow(XX,p);
    G=gcd(XP-XX);         
    parity=0;
    if (isone(G)) parity=1;
    cout << "NP mod 2 =   " << (p+1-parity)%2;
    if ((p+1-parity)%2==0)
    {                                  
        cout << " ***" << endl;
        if (search && !Edwards) {b+=1; continue; }
    }
    else cout << endl;

    nl=0; 
    accum=1;           // accumulated product of good primes

    Poly zero;
    PolyMod one,XT,YT,ZT,XL,YL,ZL,ZL2,ZT2;
    one=1;         // polynomial = 1
    zero=0;        // polynomial = 0

    PolyXY dGx,dGy,dGxx,dGxy,dGyy;
    ZZn E0b,E0bd,E2bs,E4b,E6b,Dg,Dj,Dgd,Djd,Dgs,Djs,jl,jld,p1,jd;
    ZZn E4bl,E6bl,deltal,atilde,btilde,gd,f,fd,s,Eg,Ej,Exy;
    int r,v,ld,ld1,discrim;
    ZZn M,cf[500],cft[500],ad,K,RF;
    Poly Fl,T,WP[500],H,X,Y,R;
    term *pos;

    E4b=-(A/3);
    E6b=-(B/2);
    delta=(E4b*E4b*E4b-E6b*E6b)/1728;

//
// find out how many bits we are going to need
// before Kangaroos can take over
//
    first=5;
    sl[0]=3; sl[1]=5; sl[2]=7; sl[3]=8; sl[4]=9; sl[5]=0; // do low prime powers
    SCHP=9;

    if (pbits<=256) d=pow((Big)2,64);
    else            d=pow((Big)2,72); // kangaroos do more work

    d=sqrt(p/d);

    escape=FALSE;


// Calculate Divisor Polynomials for small primes - Schoof 1985 p.485
// Set the first few by hand....
    

    P[1]=1; P[2]=2; P[3]=0; P[4]=0;

    P2[1]=1; P3[1]=1;

    P2[2]=P[2]*P[2];
    P3[2]=P2[2]*P[2];

    P[3].addterm(-(A*A),0); P[3].addterm(12*B,1);
    P[3].addterm(6*A,2)   ; P[3].addterm((ZZn)3,4);

    P2[3]=P[3]*P[3];
    P3[3]=P2[3]*P[3];

    P[4].addterm((ZZn)(-4)*(8*B*B+A*A*A),0);
    P[4].addterm((ZZn)(-16)*(A*B),1);
    P[4].addterm((ZZn)(-20)*(A*A),2);
    P[4].addterm((ZZn)80*B,3);
    P[4].addterm((ZZn)20*A,4);
    P[4].addterm((ZZn)4,6);

    P2[4]=P[4]*P[4];
    P3[4]=P2[4]*P[4];

// generation of Divisor polynomials 
// See Schoof p. 485

    for (jj=5;jj<=SCHP+1;jj++)
    { // different for even and odd 
        if (jj%2==1)
        { 
            n=(jj-1)/2;
            if (n%2==0)
                P[jj]=P[n+2]*P3[n]*Y4-P3[n+1]*P[n-1];
            else
                P[jj]=P[n+2]*P3[n]-Y4*P3[n+1]*P[n-1];
        }
        else
        {
            n=jj/2;
            P[jj]=P[n]*(P[n+2]*P2[n-1]-P[n-2]*P2[n+1])/(ZZn)2;
      
        }
        if (jj <= 1+(SCHP+1)/2)
        { // precalculate for later
            P2[jj]=P[jj]*P[jj];
            P3[jj]=P2[jj]*P[jj];
        }
    }

//
// Schoof's original method for small primes
//

    for (i=0;;i++)
    {
        lp=sl[i];
        if (lp==0) break;

        if (lp>=first)
        {
            good[nl]=lp;
            accum*=lp;
        }
        k=p%lp;

        setmod(P[lp]);
        MY2=Y2;
// These next are time-consuming calculations of X^P, X^(P*P), Y^P and Y^(P*P)

        cout << "X^P " << flush;
        XP=pow(XX,p);
        cout << "\b\b\b\bY^P " << flush;
        YP=pow(MY2,(p-1)/2);

        cout << "\b\b\b\bX^PP" << flush;
        XPP=compose(XP,XP);   // this is faster
        cout << "\b\b\b\bY^PP" << flush;
        YPP=YP*compose(YP,XP);
        cout << "\b\b\b\b";

        PolyMod Pk,P2k,PkP1,PkM1,PkP2;
        Pk=P[k]; PkP1=P[k+1]; PkM1=P[k-1]; PkP2=P[k+2];

        P2k=(Pk*Pk);
//
// This is Schoof's algorithm, stripped to its bare essentials
//
// Now looking for the value of tau which satisfies 
// (X^(P*P),Y^(P*P)) + k.(X,Y) =  tau.(X^P,Y^P)
// 
// Note that (X,Y) are rational polynomial expressions for points on
// an elliptic curve, so "+" means elliptic curve point addition
// 
// k.(X,Y) can be found directly from Divisor polynomials
// Schoof Prop (2.2)
//
// Points are converted to projective (X,Y,Z) form
// This is faster (x2). Observe that (X/Z^2,Y/Z^3,1) is the same
// point in projective co-ordinates as (X,Y,Z)
//

        if (k%2==0)
        {
            XT=XX*MY2*P2k-PkM1*PkP1;
            YT=(PkP2*PkM1*PkM1-P[k-2]*PkP1*PkP1)/4;
            XT*=MY2;      // fix up, so that Y has implicit y multiplier
            YT*=MY2;      // rather than Z
            ZT=MY2*Pk;
        }
        else
        {
            XT=(XX*P2k-MY2*PkM1*PkP1);
            if (k==1) YT=(PkP2*PkM1*PkM1+PkP1*PkP1)/4;
            else      YT=(PkP2*PkM1*PkM1-P[k-2]*PkP1*PkP1)/4;
            ZT=Pk;
        }

        elliptic_add(XT,YT,ZT,XPP,YPP);

// 
// Test for Schoof's case 1 - LHS (XT,YT,ZT) is point at infinity
//

        cout << "NP mod " << lp << " = " << flush;
        if (iszero(ZT))
        { // Is it zero point? (XPP,YPP) = - K(X,Y)
            if (lp>=first)  t[nl++]=0;
            cout << setw(3) << (p+1)%lp;
            if ((p+1)%lp==0)
            {      
                cout << " ***" << endl;
                if (search && (!Edwards || lp!=4)) {escape=TRUE; break;}
            }
            else cout << endl;
            continue;         
        }
//
// Now keep finding tau.(X^P,Y^P), until equality is detected
// This is very simple!
//
        XL=XP;
        YL=YP;
        ZL=1;
        ZT2=ZT*ZT;
        for (tau=1;tau<=(lp/2);tau++)
        { 
            cout << setw(3) << (p+1-tau)%lp << flush;     

            ZL2=ZL*ZL;
            if (iszero(XT*ZL2-ZT2*XL))   // LHS == RHS??
            { // LHS = RHS
                if (!iszero(YT*ZL2*ZL-YL*ZT*ZT2))
                { // point doubled - change sign
                    tau=lp-tau;
                    cout << "\b\b\b";
                    cout << setw(3) << (p+1-tau)%lp << flush;     
                }
                if (lp>=first) t[nl++]=tau;
                if ((p+1-tau)%lp==0)
                {
                    cout << " ***" << endl;
                    if (search && (!Edwards || lp!=4)) escape=TRUE;
                }
                else cout << endl;
                break;
            }
            elliptic_add(XL,YL,ZL,XP,YP);
            cout << "\b\b\b";            
        }
        if (escape) break;       
    }

    if (!escape) for (i=1;accum<=d;i++)      
    {
        if (i>max)
        {
            cout << "WARNING: Ran out of Modular Polynomials!" << endl;
            break;
        }
        lp=l[i];

        if (lp<=SCHP) continue;

        k=p%lp;
        for (is=1;;is++)
            if (is*(lp-1)%12==0) break;

        el=lp;
        s=is;

// Get next Modular Polynomial

        MP=Gl[i];

// Evaluate bivariate polynomial at Y=j-invariant
// and use as polynomial modulus

        F=MP.F(j);
        setmod(F);
        cout << setw(3) << lp << flush;
        XP=pow(XX,p);
//
// Determine "Splitting type" 
//
        cout << "\b\b\bGCD" << flush;
        G=gcd(XP-XX);

        if (degree(G)==lp+1) 
        {
            cout << "\b\b\b" << flush;
            continue;      // pathological case
        }
        if (degree(G)==0)  // Atkin Prime
        {
            if (!atkin && lp>100)    // Don't process large Atkin Primes
            {
                cout << "\b\b\b" << flush;
                continue;
            }
            BOOL useful=FALSE;
            cout << "\b\b\b" << flush;
            cout << "ATK" << flush;

            PolyMod u[20];
            int max_r,lim=1;
            u[0]=XP;  
            u[1]=compose(u[0],u[0]);

//
// The code for processing Atkin Primes is in here, but currently largely 
// unused. However the simplest case is used, as it suggests only one 
// value for NP mod lp, and so can be used just like an Elkies prime
// 
//
            if (atkin) max_r=lp+1;
            else       max_r=2;
            for (r=2;r<=max_r;r++)
            {
                PolyMod C;
                int kk,m;
                BOOL first;
                if ((lp+1)%r!=0) continue;    // only keep good ones!
                v=jac(k,lp);     // check Schoof Prop. 6.3
                jj=(lp+1)/r;
                if (jj%2==0 && v==(-1)) continue;
                if (jj%2==1 && v==1) continue;
       //         if (phi(r)>8) continue;       // > 8 candidates
       //         if (lp<30 && phi(r)>2) continue;
       //         if (lp<60 && phi(r)>4) continue;
                kk=r; m=0;
                first=TRUE;
//
// Right-to-Left Power Composition - find X^(P^r)
//
                forever
                {
                    if (kk%2!=0)
                    {
                        if (first) C=u[m]; 
                        else       C=compose(u[m],C);
                        first=FALSE;
                    }
                    kk/=2;
                    if (kk==0) break;
                    m++;
                    if (m>lim) 
                    { // remember them for next time
                        u[m]=compose(u[m-1],u[m-1]);
                        lim=m;
                    }
                }

                if (iszero(C-XX)) 
                { // found splitting type
                    useful=TRUE;
                    break;
                }
            }
            cout << "\b\b\b" << flush;
            if (!useful) continue;

            cout << "NP mod " << lp << " = " << flush;

            int a,b,candidates,gx,gy,ord,qnr=2;
            BOOL gen;
            while (jac(qnr,lp)!=(-1)) qnr++;

//
// [4] Algorithm VII.4 - find a generator of F(lp^2)
//
            ord=lp*lp-1;
            gy=1;
            for (gx=1;gx<lp;gx++)
            {
                gen=TRUE;
                for (jj=2;jj<=ord/2;jj++)
                {
                    if (ord%jj!=0) continue;
                    powquad(lp,qnr,gx,gy,ord/jj,a,b);
                    if (a==1 && b==0) {gen=FALSE; break;}
                }
                if (gen) break;
            }
//
// (gx,gy) is a generator
//
            candidates=0;
            cout << setw(3);
            for (jj=1;jj<r;jj++)
            {
                if (jj>1 && igcd(jj,r)!=1) continue;
                powquad(lp,qnr,gx,gy,jj*ord/r,a,b);

                tau=((a+1)*k*(int)invers(2,lp))%lp;
                if (tau==0)
                {           // r must be 2 - I can make use of this!
                            // Its an Atkin prime, but only one possibility
                    candidates++;
                    cout << (p+1)%lp << flush;
                    if ((p+1)%lp==0)
                    {
                        cout << " ***" << endl;
                        if (search && (!Edwards || lp!=4)) escape=TRUE;
                    }
                    else cout << endl; 
                    good[nl]=lp;
                    t[nl]=tau;
                    nl++;
                    accum*=lp;  
                    break;
                }
                else if (jac(tau,lp)==1)
                {
                    candidates+=2;
                    tau=sqrmp(tau,lp);
                    tau=(2*tau)%lp;
                    if (candidates==phi(r))
                    { 
                         cout << (p+1-tau)%lp << " or " << (p+1+tau)%lp << endl;   
                         break;
                    }
                    else cout << (p+1-tau)%lp << "," << (p+1+tau)%lp << "," << flush;
                }  
            }
            if (escape) break;
            continue;  
        }

//
// Good Elkies prime - so use it!
//
// First solve quadratic for a root
//
        if (degree(G)==1)
        {
            discrim=0; 
            g=-G.coeff(0); // Elkies Prime, one root, (2 possibilites)   
        }
        else               // degree(G)==2
        {                  // Elkies Prime, two roots
            discrim=1;
            qb=G.coeff(1);
            qc=G.coeff(0); 
            g=sqrt(qb*qb-4*qc);
            g=(-qb-g)/2;   // pick either one
        }
        cout << "\b\b\bELK" << flush;
//
// Mueller's procedure for finding the atilde, btilde and p1
// parameters of the isogenous curve
// 3. page 111
// 4. page 131-133
// First we need partial differentials of bivariate Modular Polynomial
//

        dGx=diff_dx(MP);
        dGy=diff_dy(MP);
        dGxx=diff_dx(dGx);
        dGxy=diff_dx(dGy);
        dGyy=diff_dy(dGy);

        Eg=dGx.F(g,j);   // Evaluated at (g,j)
        Ej=dGy.F(g,j);
        Exy=dGxy.F(g,j);

        Dg=g*Eg;    
        Dj=j*Ej;

        deltal=delta*pow(g,12/is)/pow(el,12);

        if (Dj==0)
        {
            E4bl=E4b/(el*el);
            atilde=-3*pow(el,4)*E4bl;
            jl=pow(E4bl,3)/deltal;
            btilde=2*pow(el,6)*sqrt((jl-1728)*deltal);
            p1=0;
        }
        else
        {
            E2bs=(-12*E6b*Dj)/(s*E4b*Dg);

            gd=-(s/12)*E2bs*g;
            jd=-E4b*E4b*E6b/delta;
            E0b=E6b/(E4b*E2bs); 

            Dgd=gd*Eg+g*(gd*dGxx.F(g,j)+jd*Exy);
            Djd=jd*Ej+j*(jd*dGyy.F(g,j)+gd*Exy);  
   
            E0bd=((-s*Dgd)/12-E0b*Djd)/Dj;

            E4bl=(E4b-E2bs*(12*E0bd/E0b+6*E4b*E4b/E6b-4*E6b/E4b)+E2bs*E2bs)/(el*el);

            jl=pow(E4bl,3)/deltal;
            f=pow(el,is)/g; fd=s*E2bs*f/12;

            Dgs=dGx.F(f,jl);
            Djs=dGy.F(f,jl);

            jld=-fd*Dgs/(el*Djs);
            E6bl=-E4bl*jld/jl;

            atilde=-3*pow(el,4)*E4bl;
            btilde=-2*pow(el,6)*E6bl;
            p1=-el*E2bs/2;            
        }

//
// Find factor of Division Polynomial from atilde, btilde and p1 
// Here we follow 3. p 116
// Polynomials have been modified s.t x=z^2
//
// Note that all Polynomials can be reduced mod x^(d+1),
// where d=(lp-1)/2, using modxn() function
//

        cout << "\b\b\bFAC" << flush;
        ld=(lp-1)/2;
        ld1=(lp-3)/2;

        get_ck(ld1,A,B,cf);

        WP[1]=1;
        pos=NULL;
        for (k=ld1;k>0;k--)
           pos=WP[1].addterm(cf[k],k+1,pos);
        for (v=2;v<=ld;v++)
            WP[v]=modxn(WP[v-1]*WP[1],ld+1);
//
// WPv have understood multiplier x^-v
//            
        get_ck(ld1,atilde,btilde,cft);

        Y=0;
        pos=NULL;
        for (k=ld1;k>0;k--)
            pos=Y.addterm((lp*cf[k]-cft[k])/(ZZn)((2*k+1)*(2*k+2)),k+1,pos);
        Y.addterm(-p1,1,pos);

        RF=1;
        H=1;
        X=1;
        for (r=1;r<=ld;r++)
        {
            X=modxn(X*Y,ld+1);
            RF*=r;
            H+=(X/RF);
        }
//
//  H has understood multiplier x^-d
//
        ad=1;
        Fl=0;
        pos=Fl.addterm(ad,ld);
        for (v=ld-1;v>=0;v--)
        {
            H-=ad*WP[v+1];
            H=divxn(H,1);
            ad=H.min();
            pos=Fl.addterm(ad,v,pos);
        }

        setmod(Fl);
        MY2=Y2;
        MY4=Y4;

//
// Only the Y-coordinate is calculated. No need for X^P !
//
        cout << "\b\b\bY^P" << flush;
        YP=pow(MY2,(p-1)/2);
        cout << "\b\b\b";

// Calculate Divisor Polynomials for small primes - Schoof 1985 p.485
// This time mod the new (small) modulus Fl
// Set the first few by hand....
    
        PolyMod Pf[300],P2f[300],P3f[300];
        Pf[0]=0; Pf[1]=1; Pf[2]=2; Pf[3]=0; Pf[4]=0;

        P2f[1]=1; P3f[1]=1;

        P2f[2]=Pf[2]*Pf[2];
        P3f[2]=P2f[2]*Pf[2];

        Pf[3].addterm(-(A*A),0); Pf[3].addterm(12*B,1);
        Pf[3].addterm(6*A,2)   ; Pf[3].addterm((ZZn)3,4);

        P2f[3]=Pf[3]*Pf[3];
        P3f[3]=P2f[3]*Pf[3];

        Pf[4].addterm((ZZn)(-4)*(8*B*B+A*A*A),0);
        Pf[4].addterm((ZZn)(-16)*(A*B),1);
        Pf[4].addterm((ZZn)(-20)*(A*A),2);
        Pf[4].addterm((ZZn)80*B,3);
        Pf[4].addterm((ZZn)20*A,4);
        Pf[4].addterm((ZZn)4,6);

        P2f[4]=Pf[4]*Pf[4];
        P3f[4]=P2f[4]*Pf[4];
        lower=5;
        
//
// Now looking for value of lambda which satisfies
// (X^P,Y^P) = lambda.(XX,YY). 
// 3. Page 118, Algorithm 7.9
//
// Note that it appears to be sufficient to only compare the Y coordinates (!?)
// For a justification see page 120 of 3. 
// Thank you SYSTRAN translation service! (www.altavista.com)
//
        good[nl]=lp;
        cout << "NP mod " << lp << " = " << flush;
        for (lambda=1;lambda<=(lp-1)/2;lambda++)
        {
            int res=0;
            PolyMod Ry,Ty;
            tau=(lambda+invers(lambda,lp)*p)%lp;

            k=(lp+tau*tau-(4*p)%lp)%lp;
            if (jac(k,lp)!=discrim) continue; 
//
//  Possible values of tau could be eliminated here by an application of 
//  Atkin's algorithm....  
//  
            cout << setw(3) << (p+1-tau)%lp << flush; 

      // This "loop" is usually executed just once
            for (jj=lower;jj<=lambda+2;jj++)
            { // different for even and odd 
                if (jj%2==1)     // 2 mod-muls
                { 
                    n=(jj-1)/2;
                    if (n%2==0)
                        Pf[jj]=Pf[n+2]*P3f[n]*MY4-P3f[n+1]*Pf[n-1];
                    else
                        Pf[jj]=Pf[n+2]*P3f[n]-MY4*P3f[n+1]*Pf[n-1];
                }
                else            // 3 mod-muls
                {
                    n=jj/2;
                    Pf[jj]=Pf[n]*(Pf[n+2]*P2f[n-1]-Pf[n-2]*P2f[n+1])/(ZZn)2;
                }
                P2f[jj]=Pf[jj]*Pf[jj];     // square
                P3f[jj]=P2f[jj]*Pf[jj];    // cube
            }
            if (lambda+3>lower) lower=lambda+3;

     // compare Y-coordinates - 3 polynomial mod-muls required

            if (lambda%2==0)
            {
                Ry=(Pf[lambda+2]*P2f[lambda-1]-Pf[lambda-2]*P2f[lambda+1])/4;
                Ty=MY4*YP*P3f[lambda];
            }
            else
            {
                if (lambda==1) Ry=(Pf[lambda+2]*P2f[lambda-1]+P2f[lambda+1])/4;
                else           Ry=(Pf[lambda+2]*P2f[lambda-1]-Pf[lambda-2]*P2f[lambda+1])/4;
                Ty=YP*P3f[lambda];
            }
            if (iszero(Ty-Ry)) res=1;
            if (iszero(Ty+Ry)) res=2;

            if (res!=0) 
            {  // has it doubled, or become point at infinity?
                if (res==2)
                { // it doubled - wrong sign
                    tau=(lp-tau)%lp;
                    cout << "\b\b\b";
                    cout << setw(3) << (p+1-tau)%lp << flush; 
                }
                t[nl]=tau;
                if ((p+1-tau)%lp==0)
                {
                    cout << " ***" << endl;
                    if (search && (!Edwards || lp!=4)) escape=TRUE;
                }
                else cout << endl;
                break;
            }
            cout << "\b\b\b";
        }
        nl++;        
        accum*=lp;
        if (escape) break;
    }
    Modulus.clear();

    if (escape) {b+=1; continue;}

    Crt CRT(nl,good);
    Big order,ordermod;
    ordermod=accum;
    order=(p+1-CRT.eval(t))%ordermod;    // get order mod product of primes

    nrp=kangaroo(p,order,ordermod);

    if (Edwards)
	{
		if (!prime(nrp/4) && search) {b+=1; continue; }
		else break;
	}
	else
	{
		if (!prime(nrp) && search) {b+=1; continue; }
		else break;
    }
    }

    if (fout) 
    {
        ECn P;
        ofile << bits(p) << endl;
        mip->IOBASE=16;
        ofile << p << endl;

        ofile << a << endl;
        ofile << b << endl;

    // generate a random point on the curve 
    // point will be of prime order for "ideal" curve, otherwise any point
		if (!Edwards)
		{
			do {
				x=rand(p);
			} while (!P.set(x,x));
			P.get(x,y);
			ofile << nrp << endl;
		}
		else
		{
			ZZn X,Y,Z,R,TA,TB,TC,TD,TE;
			forever
			{
				X=randn();
				R=(X*X-EB)/(X*X-EA);
				if (!qr(R))continue;
				Y=sqrt(R);
				break;
			}
			Z=1;
// double point twice (4*P)
			for (i=0;i<2;i++)
			{
				TA = X*X;
				TB = Y*Y;
				TC = TA+TB;
				TD = TA-TB;
				TE = (X+Y)*(X+Y)-TC;
			
				X = TC*TD;
				Y = TE*(TC-2*EB*Z*Z);
				Z = TD*TE;
			}
			X/=Z;
			Y/=Z;
			x=X;
			y=Y;
			ofile << nrp/4 << endl;
		}
        ofile << x << endl;
        ofile << y << endl;
        mip->IOBASE=10;
    }
    if (p==nrp) 
    {
        cout << "WARNING: Curve is anomalous" << endl;
   //     return 0;
    }
// check MOV condition for curves of Cryptographic interest
    d=1;
    for (i=0;i<50;i++)
    {
        d=modmult(d,p,nrp);
        if (d==1) 
        {
           cout << "WARNING: Curve fails MOV condition" << endl;		  

     //      return 0;
        }
    }
	int xxx;
 cin>>xxx;

//	return 0;
}

