#include <iostream>
#include <fstream>
#include <cmath>
#include <sstream>
using namespace std;
typedef unsigned short int suint;
const unsigned int MAX_LN_FIL = 12000000, MAX_2N=32,MAX_N=16, MAX_CYC = 10000;

suint L[MAX_N], R[MAX_N], PosL[MAX_N], tpL[MAX_N], tpR[MAX_N], tpPosL[MAX_N], PosR[MAX_N], tpPosR[MAX_N], VrtxDFS[MAX_N]= {0}, PosVrtxDFS[MAX_N]= {0};
suint LisGenDet[MAX_N], LisSizDet[MAX_N], Matbeg[MAX_N];
suint tpLk[MAX_N][MAX_N], tpPosLk[MAX_N][MAX_N];
suint FIL[MAX_CYC][MAX_N]= {0}, CFIL[MAX_CYC][MAX_N]= {0},Indx[MAX_CYC][MAX_N]= {0};
suint lnc[MAX_CYC]= {0};
suint Dsz[MAX_CYC][MAX_N]= {0}, Hsz[MAX_CYC][MAX_N]= {0};
suint ALLGl[MAX_LN_FIL][MAX_2N];
int SymM[MAX_LN_FIL];
int ic[MAX_N], jc[MAX_N];
static unsigned int LN = 0, v = 0, dv = 1;
static bool syy = false;
int v1, v2, jdfs = 1;
inline void Swap(suint *L, suint *PosL, int v1, int v2)
{
    swap(L[v1],L[v2]);
    PosL[L[v1]]=v1;
    PosL[L[v2]]=v2;
    swap(L[PosL[v1]],L[PosL[v2]]);
    swap(PosL[v1],PosL[v2]);
    return;
}

inline bool Mini(suint *L1, suint *L2, const int n)
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

inline void ADD(suint *L1, suint *L2, int n)
{
    for(int k=1; k<=n; k++)
        L1[k]=L2[k];
}

inline bool Equal(suint *L1,suint* L2, const int n)
{
    for(int i=1; i<=n; i++)
        if(L1[i]!=L2[i])
            return false;
    return true;
}

inline void recswap(int q, int k, suint *L, suint *PosL)
{
    v1=Indx[q][k-1]+1;
    v2=Indx[q][k];
    Swap(L, PosL, v1, v2);
    for(int i=1; i<=CFIL[q][k]-2; i++)
    {
        v1=Indx[q][k]-i+1;
        v2=Indx[q][k]-i;
        Swap(L, PosL, v1, v2);
    }

    return;
}

inline void REV(int q, int k, suint *L, suint *PosL)
{
    for(int i=0; i<Hsz[q][k]; i++)
    {
        v1=Indx[q][k-1]+1+i;
        v2=Indx[q][k]-i;
        Swap(L,PosL, v1,v2);
    }

    return;
}

inline void FindR(int q, int k, suint *L, suint *PosL)
{
    v1=Indx[q][k-1]+1;
    v2=Indx[q][k];
    swap(L[v1],L[v2]);
    //swap(Lc[v1],Lc[v2]);
    PosL[L[v1]]=v1;
    PosL[L[v2]]=v2;
    for(int i=1; i<=CFIL[q][k]-2; i++)
    {
        v1=i+Indx[q][k-1];
        v2=i+Indx[q][k-1]+1;
        swap(L[v1],L[v2]);
        //  swap(Lc[v1],Lc[v2]);
        PosL[L[v1]]=v1;
        PosL[L[v2]]=v2;
    }
    return;
}

void DFSUtil(int v, bool visited[], suint *L, suint *R)
{
    visited[v] = true;
    VrtxDFS[jdfs] = v;
    jdfs++;
    if(!visited[L[v]])
        DFSUtil(L[v], visited,L,R);
    if(!visited[R[v]])
        DFSUtil(R[v], visited,L,R);
}

void PropreLabel(suint *L, suint *R, suint *PosL, suint *PosR, const int n)
{
    suint v1,v2;
    bool visited[n+1] = {false};
    jdfs = 1;
    DFSUtil(1, visited,L,R);

    for(int i = 1; i<=n; i++)
        PosVrtxDFS[VrtxDFS[i]] = i;

    for(int i=1; i<=n; i++)
    {
        if(VrtxDFS[i]==i) continue;
        v1 = VrtxDFS[i];
        v2 = i;
        Swap(L,PosL,v1,v2);
        Swap(R,PosR,v1,v2);
    }
    return;
}

bool PermuteFiltre(int q, int p, suint *L, suint *tpL,suint *tpPosL, int szALLde, int ld, const int n)
{

    if(syy)
        return syy;
    if(p==LisGenDet[ld]+1)
    {
        ld++;
        if(ld==szALLde+1)
        {
            if(Equal(L,tpL,n))
            {
                //printL(Lc,n);
                /*if(!Equal(Lc,Lc0,n))
                {
                ADD(MatS[dvc],Lc,n);
                dvc++;
                }*/

                dv++;
            }
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
                {
                    v1=Indx[q][i+Matbeg[ld]-1]+1+j;
                    v2=Indx[q][p+Matbeg[ld]-1]+1+j;
                    Swap(tpL, tpPosL, v1, v2);
                }
            PermuteFiltre(q,p+1, L,tpL, tpPosL, szALLde,ld, n);
            if(i!=p)
                for(int j=0; j<LisSizDet[ld]; j++)
                {
                    v1=Indx[q][i+Matbeg[ld]-1]+1+j;
                    v2=Indx[q][p+Matbeg[ld]-1]+1+j;
                    Swap(tpL, tpPosL, v1, v2);
                }

        }
    }
    if(syy)
        return true;
    else
        return false;
}

bool Filtre(int k, int fin, int q,suint *L, suint *tpL, suint *tpPosL, int szALLde, const int n)
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
            {
                //printL(Lc,n);
                /*if(!Equal(Lc,Lc0,n))
                {
                    ADD(MatS[dvc],Lc,n);
                    dvc++;
                }*/

                //ADD(Lc,Lc0,n);//initialize
                dv++;
            }

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



bool Itir(int p, int q, int szALLde, int sig, const int n)
{
    int i, j, k;
    bool hf;

    if(p==n+1)
    {
        for(k=1; k<=lnc[q]; k++)
        {
            R[Indx[q][k-1]+1]=L[Indx[q][k]];
            for(j=Indx[q][k-1]+2; j<=Indx[q][k]; j++)
                R[j]=L[j-1];
        }
        if(lnc[q] != 1)
        {
            bool visited[n+1] = {false};
            jdfs = 1;
            DFSUtil(1, visited,L,R);
        }
        if(jdfs-1 == n || lnc[q] == 1)/*if not disconnected diagrams*/
        {
            hf = false;
            for(k=1; k<=n; k++)
                if(R[k]==k||L[k]==k)
                {
                    hf = true;
                    break;
                }

            if(!hf)
            {
                ADD(tpL,L,n);
                ADD(tpPosL,PosL,n);
                dv=1;
                syy=false;
                if(!Filtre(1, lnc[q], q, L, tpL, tpPosL, szALLde, n))/*if there is not another equivalent diagram*/
                {

                    for(k=1; k<=n; k++)
                        PosR[R[k]]=k;
                    ADD(tpL,L,n);
                    ADD(tpPosL,PosL,n);
                    ADD(tpR,R,n);
                    ADD(tpPosR,PosR,n);
                    PropreLabel(tpL,tpR,tpPosL,tpPosR, n);

                    for(k=1; k<=n; k++)
                    {
                        ALLGl[LN][2*k-1]=R[k];
                        ALLGl[LN][2*k]=L[k];
                    }

                    SymM[LN]=-sig*(dv-1);
                    LN++;
                }
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
    for(suint q=0; q<v; q++)
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

void write_L(const int n)
{
    ofstream myfile;
    myfile.open("HugenDiag.txt");
    myfile<<"Diag = {";
    for(unsigned int ff=0; ff<LN-1; ff++)
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
    for(unsigned int ff=0; ff<LN-1; ff++)
        myfile<<SymM[ff]<<",";
    myfile<<SymM[LN-1]<<"};";
    myfile<<endl;
    myfile.close();
    return;
}

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
