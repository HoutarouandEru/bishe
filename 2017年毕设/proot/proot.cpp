#include <stdio.h>
#include <iostream>
#include <gmp.h>
#include <ctime>
#include<stdlib.h>

int twofact(char *s_a_1,char *s_b_1){//2分解 
	mpz_t a_1,z_1;
    mpz_init_set_str(a_1,s_a_1,10);
    mpz_init_set_str(z_1,s_b_1,10);	    
	int k = 0;
	if (mpz_cmp_ui(a_1,0) == 0){//a_1 == 0 
		mpz_set_ui(z_1,0);//z_1 = 0
		mpz_get_str(s_b_1,10,z_1);
		return 0; 
	}	
	char ss[255];
	mpz_set(z_1,a_1);//z_1 = a_1	
	mpz_get_str(ss,10,z_1);	
	while(mpz_odd_p(z_1) ==0){
		mpz_tdiv_q_2exp(z_1,z_1,1); //除以2 
		++k;
	}
	mpz_get_str(s_b_1,10,z_1);	
	return k;
	mpz_clear(a_1);mpz_clear(z_1);}
	
int proot_2(mpz_t ai,mpz_t ki,char *x){
	mpz_t h,b,t;
	mpz_init(h);mpz_init(b);mpz_init(t);
	int j;
	mpz_set_ui(h,1);
	for(j = 0;mpz_cmp_ui(ki,j) >= 0;j++)
		 mpz_mul_ui(h,h,2);
	mpz_sqrt(b,h);
	mpz_tdiv_q_2exp(h,h,1);
	if (mpz_odd_p(b) == 0) mpz_add_ui(b,b,1);
		else mpz_add_ui(b,b,2);
	mpz_mul(t,b,b);
	mpz_sub(t,t,ai);
	while(mpz_cmp(h,t) != 0){
		mpz_sub_ui(b,b,2);
		mpz_mul(t,b,b);
		mpz_sub(t,t,ai);
		if (mpz_cmp_ui(b,0)<0){
									printf("No answer in proot_2!\n");
									return -1;
		}
	}		 
	mpz_get_str(x,10,b);
}
	
int proot_1(char *s_a_1,char *s_p_1,char *s_x_1){
    mpz_t a_1,p_1,x_1;
    mpz_init_set_str(a_1,s_a_1,10);
    mpz_init_set_str(p_1,s_p_1,10);
    mpz_init_set_str(x_1,s_x_1,10);    
	mpz_t z_1,q_1,t_1,y_1,n_1,exp2;
	mpz_init(z_1);mpz_init(q_1);mpz_init(t_1);mpz_init(y_1);mpz_init(n_1);mpz_init(exp2);
	int r,m;	
	if (mpz_jacobi(a_1,p_1) != 1) {
		printf("(a/p) = %d\n",mpz_jacobi(a_1,p_1));
		return -1;
	}
	if (mpz_cmp_ui(p_1,0) == 0|| mpz_odd_p(p_1) ==0){//p_1 == 0 || p_1为偶数 
		return -1;
	}		
	if (mpz_cmp_ui(a_1,0) == 0){//a_1 == 0
		mpz_init_set_ui(x_1,0); //x_1 = 0; 
		return 0;
	}	
	////////////////找二次非剩余/////////////// 
	mpz_sub_ui(q_1,p_1,1);//q_1 = p_1 -1	
	char s_q_1[255];
	mpz_get_str(s_q_1,10,q_1);//转换 
	r = twofact(s_q_1,s_q_1);/////分解 
   	mpz_init_set_str(q_1,s_q_1,10);//转换 
	mpz_set_ui(n_1,2);//n_1 = 2 
	while (mpz_jacobi(n_1,p_1) == 1){//jacobi n_1/p_1
		mpz_add_ui(n_1,n_1,1);//n++ 
	}	
//	gmp_printf("n = %Zd\n",n_1);
    ////////////////递归初始化//////////////////
	mpz_powm(n_1,n_1,q_1,p_1);//模幂 底数n_1 指数q_1 模数p_1 n_1 = n_1 ^ q_1 
	mpz_set(y_1,n_1);//y_1 = n_1
	mpz_sub_ui(q_1,q_1,1);//q_1 = q_1 - 1	
	mpz_tdiv_q_2exp(q_1,q_1,1);	//q_1 = q_1 /2 	
	mpz_powm(x_1,a_1,q_1,p_1);//置rop 为base^exp mod mod。		
	mpz_powm_ui(z_1,x_1,2,p_1);//模平方 msqr()
	mpz_mul(z_1,a_1,z_1);mpz_mod(z_1,z_1,p_1);//  a_1 * z_1 mod p_1
	mpz_mul(x_1,a_1,x_1);mpz_mod(x_1,x_1,p_1);//  a_1 * x_1 mod p_1
	mpz_mod(q_1,z_1,p_1);
/*	
	gmp_printf("x = %Zd\n",x_1);
	gmp_printf("y = %Zd\n",y_1);
	gmp_printf("q = %Zd\n",q_1);
	gmp_printf("z = %Zd\n",z_1);
	printf("m = %d   r = %d \n",m,r);
	
*/		
	while (mpz_cmp_ui(q_1,1) != 0){
			m = 0;
			do{
				++m;
			mpz_powm_ui(q_1,q_1,2,p_1);//置rop 为base^exp mod mod。 msqr()
			}	while (mpz_cmp_ui(q_1,1) != 0);
			if (m == r)	return -1;
			mpz_set_ui(exp2,1);
    		mpz_mul_2exp(exp2,exp2,(r - m - 1));// exp2 = 2 ^ (r - m - 1)
    		mpz_powm(t_1,y_1,exp2,p_1);//   t_1 = y_1 ^exp2 mod p_1    
			mpz_mul(x_1,t_1,x_1);mpz_mod(x_1,x_1,p_1);//  x_1 = t_1 * x_1 mod p_1
			mpz_mul(y_1,t_1,t_1);mpz_mod(y_1,y_1,p_1);//  y_1 = t_1 * t_1 mod p_1	
			mpz_mul(z_1,z_1,y_1);mpz_mod(z_1,z_1,p_1);//  z_1 = z_1 * y_1 mod p_1
			mpz_set(q_1,z_1);
			r = m;
	}/*	
	printf("m = %d\n\n",m);
	gmp_printf("t = %Zd\n",t_1);
	gmp_printf("x = %Zd\n",x_1);
	gmp_printf("y = %Zd\n",y_1);
	gmp_printf("q = %Zd\n",q_1);
	gmp_printf("z = %Zd\n",z_1);
	printf("m = %d   r = %d \n",m,r);
*/	
	mpz_get_str(s_x_1,10,x_1);
	mpz_clear(a_1);mpz_clear(p_1);mpz_clear(x_1);mpz_clear(q_1);mpz_clear(exp2);
	return 0;
}
int proot_n(char *s_x,char *s_a,char *s_p,char *s_k){
	mpz_t a,p,x,k;
	mpz_t x1,x2,temp,tm,tp;
	int t,ttm;	
	char ss[255];	
	mpz_init(a);mpz_init(p);mpz_init(x);mpz_init(k);mpz_init(x1);mpz_init(x2);mpz_init(temp);mpz_init(tm);
	mpz_init_set_str(a,s_a,10);
	mpz_init_set_str(p,s_p,10);	
	mpz_init_set_str(k,s_k,10);
	mpz_init_set_ui(tp,1);
	t = proot_1(s_a,s_p,s_x);
	
	if (t != 0 || mpz_cmp_ui(k,1) < 0) {
		printf("error in proot_n!\n");
		return -1;
	}
	mpz_init_set_str(x,s_x,10);		
	mpz_init_set_str(x1,s_x,10);
	while(mpz_cmp_ui(k,1) > 0){//解一次同余方程   x = b * a ^ p - 1 -1 (mod p) 		
		mpz_mul(temp,x1,x1);		
		mpz_sub(temp,temp,a);
		mpz_tdiv_q(temp,temp,p);
		mpz_mul_ui(tm,x1,2);
		mpz_invert(x2,tm,p);
        mpz_mul(tp,tp,p);
		mpz_neg(temp,temp);
		mpz_mul(x2,x2,temp);
		mpz_mod(x2,x2,tp);
		mpz_mul(x2,x2,p);
		mpz_add(x,x1,x2);
		mpz_sub_ui(k,k,1);
		mpz_set(x1,x); 
	}	
	mpz_get_str(s_x,10,x);
	mpz_clear(a);mpz_clear(p);mpz_clear(x);mpz_clear(k);mpz_clear(x1);mpz_clear(x2);mpz_clear(temp);mpz_clear(tm);mpz_clear(tp);
	return 0;
}
int chinrem(int n,mpz_t *ai,mpz_t *pi,mpz_t x){
	mpz_t p,u,v,g,temp;
	mpz_init(p);mpz_init(u);mpz_init(v);mpz_init(g);mpz_init(temp);
	char s_x[255];
	int i = 0;
	if (n < 1) {
		printf("Error in chinrem!\n");
		return -1;
	}
	mpz_init_set(p,pi[0]); 
	mpz_init_set(x,ai[0]);
	while(i != n - 1){
		i++;
	//	gmp_printf("x%d = %Zd p%d = %Zd\n",i,x,i,p);
		mpz_gcdext(g,u,v,p,pi[i]);
		if (mpz_cmp_ui(g,1) != 0) {
			printf("Error in pi and p!\n");
			return -1;
		}
		mpz_mul(temp,u,ai[i]);
		mpz_mul(temp,temp,p);
		mpz_mul(x,x,v);
		mpz_mul(x,x,pi[i]);
		mpz_add(x,x,temp);
		mpz_mul(p,pi[i],p);
		mpz_mod(x,x,p);		
	}
	mpz_clear(p);mpz_clear(u);mpz_clear(v);mpz_clear(g);mpz_clear(temp); 
	return 0;
}

int main(){
	mpz_t a[50],p[50],k[50],x,M,A,N;
	int n,t;
	
	mpz_init(x);mpz_init(M);mpz_init(A);mpz_init(N);
	char sx[255],sa[255],sp[255],sk[255];
	printf("输入方程组个数：\n");
	scanf("%d",&n);
	for(int i = 0;i < n;i++){
		printf("Enter a%d,p%d,k%d\n",i+1,i+1,i+1);
		mpz_init(a[i]);mpz_init(p[i]);mpz_init(k[i]);
		gmp_scanf("%Zd%Zd%Zd",a[i],p[i],k[i]);
		if (mpz_cmp(a[i],p[i])> 0 ){
			printf("Error! a%d > p%d \n",i+1,i+1);
			return -1;
		}
	} 
	for (int i =0;i< n;i++){
		mpz_get_str(sa,10,a[i]);
		mpz_get_str(sp,10,p[i]);
		mpz_get_str(sk,10,k[i]);
		if (i == 0) mpz_set(A,a[i]);
			else if (mpz_cmp(A,a[i]) ==0) mpz_set(A,a[i]);
					else {
						printf("Wrong with a!\n");
						return 0;
					}
	//	int proot_n(char *s_x,char *s_a,char *s_p,char *s_k)
		if(mpz_cmp_ui(p[i],2) == 0) t = proot_2(a[i],k[i],sx); 
		else t = proot_n(sx,sa,sp,sk);		
				
		if (t != 0) {
			printf("No answer!\n");
			return -1;
		}
		printf("第%d个方程的解:%s\n",i+1,sx);
		mpz_set_str(a[i],sx,10);
	//	gmp_printf("a%d = %Zd\n",i+1,a[i]);
	}
	mpz_set_ui(M,1);
    for (int i = 0;i < n ;i++)
    {
    	mpz_set_ui(N,1);
    	for (int j = 0;mpz_cmp_si(k[i],j)>0;j++)
    	 mpz_mul(N,N,p[i]);
    	mpz_set(p[i],N);
		mpz_mul(M,M,N); 
	}
	chinrem(n,a,p,x);//计算x 
	gmp_printf("方程x^2 = %Zd mod %Zd的解为x = %Zd\n",A,M,x);
	system("pause");
	return 0;	
	
 
}
