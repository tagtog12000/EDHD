#include <iostream>
#include <fstream>
#include <cmath>
#include <sstream>
using namespace std;
typedef short int uint;
const unsigned int MAX_LN_FIL = 12000000, MAX_2N=32,MAX_N=16, MAX_CYC = 10000;
int NumCyEv(int p);
bool Itir(int, int, int, int, const int);
bool Filtre(int, int, int, uint*, uint*, uint*, int, const int);
bool PermuteFiltre(int, int, uint*, uint*, uint*, int, int, const int);
void Distrib(int, int, const int);
void CycGen(const int);
int Init(int, const int);
inline bool NotDiscStat(uint*, uint*, int, const int);
inline bool Equal(uint*,uint*, const int);
inline bool Mini(uint*, uint*, const int);
inline void ADD(uint *L1, uint *L2, const int);
inline void recswap(int, int, uint*, uint*);
inline void REV(int, int, uint*, uint*);
inline void FindR(int, int, uint*, uint*);
inline void Swap(uint*, uint*, const int, const int);
void write_L(const int n);
uint L[MAX_N], R[MAX_N], PosL[MAX_N], tpL[MAX_N], tpR[MAX_N], tpPosL[MAX_N];
uint LisGenDet[MAX_N], LisSizDet[MAX_N], Matbeg[MAX_N];
uint tpLk[MAX_N][MAX_N], tpPosLk[MAX_N][MAX_N];
uint FIL[MAX_CYC][MAX_N]= {0}, CFIL[MAX_CYC][MAX_N]= {0},Indx[MAX_CYC][MAX_N]= {0};
uint lnc[MAX_CYC]= {0};
uint Dsz[MAX_CYC][MAX_N]={0}, Hsz[MAX_CYC][MAX_N]={0};
uint ALLGl[MAX_LN_FIL][MAX_2N];
int SymM[MAX_LN_FIL];
int ic[MAX_N], jc[MAX_N];
static unsigned int tt=0, LN = 0, v = 0, dv = 1;
static bool syy = false;

int main()
{
    int n;
    cout << "Enter the order n" << endl;
    cin>>n;
    CycGen(n);
    Distrib(v, -1, n);//-1 for fermions and +1 for bosons
    cout << "All "<<LN<<" diagrams saved in HugenDiag.txt"<< endl;
    write_L(n);
    return 0;
}

void CycGen(const int n)
{
    ic[0]=1;
    jc[0]=n;
    ic[1]=ic[0];
    jc[1]=jc[0]-ic[0];
    NumCyEv(1);
    FIL[v][n]=1;
    v++;
    int r = 1;
    for(int q=0; q<v; q++)
    {
        r=1;
        for(int k=1; k<=n; k++)
        {
            lnc[q]+=FIL[q][k];
            if(FIL[q][k]!=0)
            {
                for(int l=1; l<=FIL[q][k]; l++)
                {
                    CFIL[q][r]=k;
                    Dsz[q][r] = 2*CFIL[q][r];
                    Hsz[q][r] = CFIL[q][r]/2;
                    Indx[q][r]=k;
                    Indx[q][r]+=Indx[q][r-1];
                    r++;
                }
            }
        }

    }
    return;
}

int Init(int q, const int n)
{
    for(int i=1; i<=n; i++)
    {
        L[i] = i;
        PosL[i] = i;
        LisGenDet[i]=0;
        LisSizDet[i]=0;
        Matbeg[i]=0;
    }
    int r = 1, j = 1;
    for(int i=1; i<=n; i++)
    {
        if(FIL[q][i]!=0)
        {
            if(FIL[q][i]>1)
            {
                LisGenDet[r]=FIL[q][i];
                LisSizDet[r]=i;
                Matbeg[r]=j-1;
                r++;
            }
            j=j+FIL[q][i];
        }
    }
    return r-1;
}

void Distrib(int v, int eps, const int n)
{
    int szALLdet = 0;
    for(int q=0; q<v; q++)
    {
        szALLdet = Init(q,n);
        int sig = 1;
        if(eps == -1)
            for(int k=1; k<=lnc[q]; k++)
                sig=sig*eps;
        else
            sig = pow(-1,n);
        Itir(1,q,szALLdet, sig, n);
    }
    return;
}

bool Itir(int p, int q, int szALLde, int sig, const int n)
{
    int i, j, k;
    if(p==n+1)
    {
        for(k=1; k<=lnc[q]; k++)
        {
            R[Indx[q][k-1]+1]=L[Indx[q][k]];
            for(j=Indx[q][k-1]+2; j<=Indx[q][k]; j++)
                R[j]=L[j-1];
        }
        if(NotDiscStat(L,R,q,n))
        {
            ADD(tpL,L,n);
            ADD(tpPosL,PosL,n);
            dv=1;
            syy=false;
            if(!Filtre(1, lnc[q], q, L, tpL, tpPosL, szALLde, n))
            {
                for(k=1; k<=n; k++)
                {
                    ALLGl[LN][2*k-1]=R[k];
                    ALLGl[LN][2*k]=L[k];
                }
                SymM[LN]=sig*(dv-1);
                LN++;
            }
        }
    }
    else
    {
        for(i=p; i<=n; i++)
        {
            swap(L[i],L[p]);
            PosL[L[i]]=i;
            PosL[L[p]]=p;
            Itir(p+1, q, szALLde, sig, n);
            swap(L[i],L[p]);
        }
    }
    return true;
}

inline void ADD(uint *L1, uint *L2, const int n)
{
    for(int k=1; k<=n; k++)
        L1[k]=L2[k];
}

int NumCyEv(int p)
{
    while(ic[p]<=jc[p])
    {
        for(int k=1; k<=p; k++)
            FIL[v][ic[k]]++;
        FIL[v][jc[p]]++;
        v++;
        ic[p+1]=ic[p];
        jc[p+1]=jc[p]-ic[p];
        NumCyEv(p+1);
        ic[p]++;
        jc[p]--;
    }
    return 0;
}

inline bool Equal(uint *L1,uint* L2, const int n)
{
    for(int i=1; i<=n; i++)
        if(L1[i]!=L2[i])
            return false;
    return true;
}

inline bool Mini(uint *L1, uint *L2, const int n)
{
    for(int i=1; i<=n; i++)
    {
        if(L1[i]==L2[i]) continue;
        if(L1[i]>L2[i])
            return true;
        else
            break;
    }
    return false;
}

bool Filtre(int k, int fin, int q,uint *L, uint *tpL, uint *tpPosL, int szALLde, const int n)
{
    if(syy)
        return syy;
    if(k==fin+1)
    {
        if(szALLde!=0)
        {
            if(PermuteFiltre(q,1, L, tpL, tpPosL, szALLde, 1, n))
            {
                syy = true;
                return syy;
            }
        }
        else
        {
            if(Equal(L,tpL,n))
                dv++;
            if(Mini(L,tpL,n))
            {
                syy = true;
                return syy;
            }
        }
    }
    else
    {
        for(int ki=0; ki<Dsz[q][k]; ki++)
        {
            if(syy)
                break;
            if(ki==CFIL[q][k])
                REV(q, k, tpL, tpPosL);
            if(ki!=0)
                recswap(q, k, tpL, tpPosL);
            ADD(tpLk[k],tpL,n);
            ADD(tpPosLk[k],tpPosL,n);
            if(ki>=CFIL[q][k])
                FindR(q,k,tpL, tpPosL);
            Filtre(k+1, fin, q, L, tpL, tpPosL, szALLde, n);
            ADD(tpL,tpLk[k],n);
            ADD(tpPosL,tpPosLk[k],n);
        }
    }
    if(syy)
        return true;
    else
        return false;
}

bool PermuteFiltre(int q, int p, uint *L, uint *tpL,uint *tpPosL, int szALLde, int ld, const int n)
{
    if(syy)
        return syy;
    if(p==LisGenDet[ld]+1)
    {
        ld++;
        if(ld==szALLde+1)
        {
            if(Equal(L,tpL,n))
                dv++;
            if(Mini(L,tpL,n))
            {
                syy = true;
                return syy;
            }
        }
        else
            PermuteFiltre(q, 1, L, tpL,tpPosL, szALLde, ld, n);
    }
    else
    {
        for(int i=p; i<=LisGenDet[ld]; i++)
        {
            if(syy)
                break;
            if(i!=p)
                for(int j=0; j<LisSizDet[ld]; j++)
                    Swap(tpL, tpPosL, Indx[q][i+Matbeg[ld]-1]+1+j, Indx[q][p+Matbeg[ld]-1]+1+j);
             PermuteFiltre(q,p+1, L,tpL, tpPosL, szALLde,ld, n);
            if(i!=p)
                for(int j=0; j<LisSizDet[ld]; j++)
                    Swap(tpL, tpPosL, Indx[q][i+Matbeg[ld]-1]+1+j, Indx[q][p+Matbeg[ld]-1]+1+j);
        }
    }
    if(syy)
        return true;
    else
        return false;
}

inline void recswap(int q, int k, uint *L, uint *PosL)
{
    Swap(L, PosL, Indx[q][k-1]+1, Indx[q][k]);
    for(int i=1; i<=CFIL[q][k]-2; i++)
        Swap(L, PosL, Indx[q][k]-i+1, Indx[q][k]-i);
    return;
}

inline void REV(int q, int k, uint *L, uint *PosL)
{
    for(int i=0; i<Hsz[q][k]; i++)
        Swap(L,PosL, Indx[q][k-1]+1+i,Indx[q][k]-i);
    return;
}

inline void FindR(int q, int k, uint *L, uint *PosL)
{
    swap(L[Indx[q][k-1]+1],L[Indx[q][k]]);
    PosL[L[Indx[q][k-1]+1]]=Indx[q][k-1]+1;
    PosL[L[Indx[q][k]]]=Indx[q][k];
    for(int i=1; i<=CFIL[q][k]-2; i++)
        {
        swap(L[i+Indx[q][k-1]],L[i+Indx[q][k-1]+1]);
        PosL[L[i+Indx[q][k-1]]]=i+Indx[q][k-1];
        PosL[L[i+Indx[q][k-1]+1]]=i+Indx[q][k-1]+1;
        }
    return;
}

inline void Swap(uint *L, uint *PosL, const int v1, const int v2)
{
    swap(L[v1],L[v2]);
    PosL[L[v1]]=v1;
    PosL[L[v2]]=v2;
    swap(L[PosL[v1]],L[PosL[v2]]);
    swap(PosL[v1],PosL[v2]);
    return;
}

inline bool NotDiscStat(uint *L,  uint *R, int q, const int n)
{
    if(lnc[q]==1)
        return true;
    bool VL[n+1] = {false}, VR[n+1] = {false};
    int indx = 1, indx0 = 1, dis = 0, j=1;
    VR[1] = true;
    while(j<=n)
    {
        for(int i=1; i<=n; i++)
        {
            if(!VL[i]&&VR[i])
            {
                if(j==1)
            VR[1]=false;
                indx=i;
                indx0=i;
                while(true)
                {
                    indx=L[indx];
                    VL[indx]=true;
                    dis++;
                    if(indx==indx0)
                        break;
                }
                break;
            }

            else if(VL[i]&&!VR[i])
            {
                indx=i;
                indx0=i;
                while(true)
                {
                    indx=R[indx];
                    VR[indx]=true;
                    dis++;
                    if(indx==indx0)
                        break;
                }
                break;
            }
        }
        j++;
    }

    if(dis<2*n)
        return false;
    return true;
}

void write_L(const int n)
{
    ofstream myfile;
    myfile.open("HugenDiag.txt");
    myfile<<"Diag = {";
    for(int ff=0; ff<LN-1; ff++)
    {
        myfile<<"{";
        for(int k=1; k<2*n; k++)
            myfile<<ALLGl[ff][k]<<",";
        myfile<<ALLGl[ff][2*n]<<"},";
    }
    myfile<<"{";
    for(int k=1; k<2*n; k++)
        myfile<<ALLGl[LN-1][k]<<",";
    myfile<<ALLGl[LN-1][2*n]<<"}};";
    myfile<<endl;
    myfile<<"Sym = {";
    for(int ff=0; ff<LN-1; ff++)
        myfile<<SymM[ff]<<",";
    myfile<<SymM[LN-1]<<"};";
    myfile<<endl;
    myfile.close();
    return;
}
