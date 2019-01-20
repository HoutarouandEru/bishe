

#include <iostream>
#include <fstream>
#include <cstring>
#include <iomanip>
#include "ps_big.h"      // power series class
#pragma comment(lib,"miracl.lib")
using namespace std;

extern int psN;          // power series are modulo x^psN

BOOL fout;
ofstream mueller;

//
// When summing the Zk^n 0<=k<L (1. page 3, top), most terms cancel out,  
// leaving only every L-th term
//

Ps_Big phase(Ps_Big &z, int L)
{ // Keep L times every L-th element in the Power Series
    Ps_Big w;
    term_ps_big *pos=NULL;
    int i,k,zf;

// k should be first coefficient a multiple of L 

    zf=z.first();
    if (zf%L==0) k=zf;
    else
    {
            k=(zf/L)*L;
            if (zf>=0) k+=L; 
    }

    for (;k<psN;k+=L )
        pos=w.addterm(L*z.coeff(k),k,pos);

    return w;
}

void mueller_pol(int L,int s)
{ // Calculate Modular Polynomial for prime L 
  // s is smallest int such that s*(L-1)/12 is integer
    int i,j,n,v;
  
    Ps_Big klein,flt,zlt,x,y,z,f,jlt[500],c[1000],ps[1000];


// First calculate v, and hence psN - number of terms in Power Series
// 2. page 5 1st para


//    cout << "v= " << s*(L-1)/12 << endl;
    cout << "preliminaries" << flush;

    v=s*(L-1)/12;
    psN=v+2;

//
// calculate Klein=j(tau) from its definition
// Numerator x... 
//
// 1. page 2
//
    for (n=1;n<psN;n++)
    {
        Ps_Big a,b,t;
        a.addterm(n*n*n,n);     // a=n^3*x^n
        b.addterm(1,0);
        b.addterm(-1,n);
        t=a/b;
        x+=t;
    }
    x=(Big)240*x;
    x.addterm(1,0);

    x=pow(x,3);
// Denominator y...
    y=eta();
    y=pow(y,24);

    klein=x/y;
    cout << "." << flush;
    klein.divxn(1);         // divides power series by x^parameter

    psN*=L;
//    cout << "psN= " << psN << endl;
    klein=power(klein,L);   // this substitutes x^L for x in the power series
    cout << "." << flush;

// Find Fl(t), Numerator z= Dedekind eta function 
// This has a simple repeating pattern of coefficients, and so costs nothing
// to calculate 1. page 2 bottom
    

    z=eta();
// Denominator y=n(Lt)...
    y=power(z,L);
    y=(Big)1/y;       // y has only psN/L terms.
    cout << "." << flush;
    z*=y;            // z has psN terms 
    flt=pow(z,2*s);   // ^2*s - expensive
    cout << "." << flush;
    flt.divxn(v);     // times x^-v
                      // This compensates for the missing q^(1/24) part of eta

    Big w=pow((Big)L,s);
    y=power(flt,L);
    cout << "." << flush;
    zlt=w/y;          // l^s/Fl(lt) - cheap - psN/L terms in power series

    cout << "." << endl;
    y.clear();
    x.clear();

    ps[0]=L+1;
//
// Calculate Power Sums. Note that f and flt are very large objects
// with psN terms. Most other power series are in "compressed" form
// with "only" psN/L terms
//
// 1. page 3
//


//    cout << "flt= " << flt << endl;

    cout << "Power Sum   = " << flush;
    z=1;
    f=1;

    for (i=1;i<=L+1;i++)
    {
        cout << setw(3) << i << flush;
        f*=flt;    // expensive. In place multiplication discourages C++
                   // from moving large objects about
        z=z*zlt;   // cheap

        ps[i]=phase(f,L)+z;
        cout << "\b\b\b" << flush;
    }

    cout << setw(3) << L+1 << endl;

    f.clear();
    z.clear();
    flt.clear();
    zlt.clear();

    cout << "Coefficient = " << flush;
    c[0]=1;
//
// Newton's Identities - Calculate coefficients from Power Sums
//
// from a Web page somewhere and 3. page 54
//

    for (i=1;i<=L+1;i++)
    {
        cout << setw(3) << i << flush;
        c[i]=0;
        for (j=1;j<=i;j++)
              c[i]+=(ps[j]*c[i-j]);   // cheap, but lots of them

        c[i]=(-c[i])/i;
        cout << "\b\b\b" << flush;
    }

    cout << setw(3) << L+1 << endl;

    for (i=0;i<=L+1;i++) ps[i].clear(); // reclaim space
//
// Get powers of j(Lt)^i, i=1 to v
// These will be needed to determine the exponent of Y in each
// coefficient of the Modular Polynomial
//
    jlt[0]=1;
    jlt[1]=klein;

    for (i=2;i<=v;i++)
        jlt[i]=jlt[i-1]*klein;    // cheap
//
// Find Modular Polynomial, format it, and output
//
// 2. page 5, middle "Hl(X) = ..."
//
    cout << "\nG" << L << "(X,Y) = X^" << L+1 ;

    if (fout) 
    {
        mueller << L << endl;
        mueller << 1 << "\n" << L+1 << "\n" << 0 << endl;
    }

    for (i=1;i<=L+1;i++)
    {
        Big cf;
        BOOL brackets,first;
        first=TRUE;
        brackets=FALSE;
        z=c[i];            

// idea is to reduce this to an integer
// by subtracting j(Lt)^k as necessary
// The power of k required is then
// the coefficient of Y^k in G(X,Y)
// The first coefficient of c[i] tells us which j(Lt)^k to try

        if (z.first()!=0) 
        {
            brackets=TRUE;
            cout << "+(" ;
        }
   // coefficient may be a polynomial in Y
        while (z.first()!=0)    
        {
            int j=(-z.first()/L);    // index into jlt
            cf=z.coeff(z.first());   // get coefficient to be cancelled
            if (fout) mueller << cf << "\n" << L+1-i << "\n" << j << endl;
            z-=(jlt[j]*cf);
            if (cf>0 && (!first || !brackets)) cout << "+";
            first=FALSE;
            if (cf==1) cout << "Y";
            if (cf==-1) cout << "-Y";
            if (abs(cf)!=1) cout << cf << "*Y";
            if (j!=1) cout << "^" << j;
        }
        cf=z.coeff(0);
        if (fout) mueller << cf << "\n" << L+1-i << "\n" << 0 << endl;

        if (cf>0) cout << "+";
        if (brackets) cout << cf << ")*X";
        else 
        {
            if (i==L+1) 
            {
                cout << cf;
                continue;
            }
            if (cf==1) cout << "X";
            if (cf==-1) cout << "-X";
            if (abs(cf)!=1) cout << cf << "*X";
        }

        if (i!=L) cout << "^" << L+1-i ;
  // all other coefficients should now be zero
        if (z.coeff(L)!=0) 
        { // check next coefficient is zero
            cout << "\n\n Sanity Check Failed " << endl;
            exit(0);
        }
    }
    for (i=0;i<=L+1;i++) c[i].clear(); // reclaim space
    for (i=0;i<=v;i++) jlt[i].clear();
    cout << endl;

    fft_reset();
}

int main(int argc,char **argv)
{
    miracl *mip;
    int i,j,s,lo,hi,p,ip,skip;
    int primes[200];
    BOOL gothi,gotlo;
    argv++; argc--;

    if (argc<1)
    {
        cout << "Incorrect usage" << endl;
        return 0;
    }
    if (argc<2)
    {
        cout << "Error in command" << endl;
        return 0;
    }

    ip=0;
    skip=12;
    fout=FALSE;
    gothi=gotlo=FALSE;
    while (ip<argc)
    {
        if (!fout && strcmp(argv[ip],"-o")==0)
        {
            ip++;
            if (ip<argc)
            {
                fout=TRUE;
                mueller.open(argv[ip++]);
                continue;
            }
            else
            {
                cout << "Error in command line" << endl;
                return 0;
            }
        }
        if (!fout && strcmp(argv[ip],"-a")==0)
        {
            ip++;
            if (ip<argc)
            {
                fout=TRUE;
                mueller.open(argv[ip++],ios::app);
                continue;
            }
            else
            {
                cout << "Error in command line" << endl;
                return 0;
            }
        }
        if (skip==12 && strcmp(argv[ip],"-s2")==0)
        {
            ip++;
            skip=2;
            continue;
        }
        if (skip==12 && strcmp(argv[ip],"-s3")==0)
        {
            ip++;
            skip=3;
            continue;
        }
        if (skip==12 && strcmp(argv[ip],"-s6")==0)
        {
            ip++;
            skip=6;
            continue;
        }
        if (!gotlo)
        {
            lo=atoi(argv[ip++]);
            gotlo=TRUE;
            continue;
        }
        if (!gothi)
        {
            hi=atoi(argv[ip++]);
            gothi=TRUE;
            continue;
        }
        cout << "Error in command line" << endl;
        return 0;
    }
    if (!gothi || !gotlo)
    {
        cout << "Error in command line" << endl;
        return 0;
    }
    if (lo>hi || hi>1000)
    {
        cout << "Invalid range specified" << endl;
        return 0;
    }

    mip=mirsys(20,0);

    gprime(1000);         // get all primes < 1000
    for (i=0;;i++)
    {
        p=mip->PRIMES[i];
        primes[i]=p;
        if (p==0) break;
    }
    mirexit();

    for (j=0,i=1;;i++)       // lets go
    { 
        p=primes[i];
        if (p==0) break;
        if (p<lo) continue;
        if (p>hi) break;
        for (s=1;;s++)
            if (s*(p-1)%12==0) break;
        if (s>=skip) continue;

        mirsys(1+(p*s)/6,0);  
        set_io_buffer_size(4096);
        j++;
        cout << "prime " << j << " = " << p << " (s=" << s << ")" << endl; 
        cout << 32*(1+(p*s)/6) << " bits reserved for each coefficient" << endl;
        mueller_pol(p,s); 
        mirexit();
    }
    cout << endl;
    if (j==0) cout << "No primes processed in the specified range" << endl;
    if (j==1) cout << "One prime processed in the specified range" << endl;
    if (j>1) cout << j << " primes processed in the specified range" << endl;
	getchar();
    return 0;   
}

