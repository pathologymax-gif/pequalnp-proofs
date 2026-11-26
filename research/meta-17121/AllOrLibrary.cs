using System;
using System.Collections.Generic;
using System.IO;

// Enumerate all pure-OR libraries with 3, 4, or 5 distinct shared nodes.
// Cases with independent shared gates have already been certified.
class AllOrLibrary {
    const uint T=16383,N=~T;
    static uint[] Raw, Join=new uint[1024], Cols=new uint[10];
    static uint[,] Miss=new uint[1024,14];
    static int[] Pop=new int[16384], Cover=new int[16384], X=new int[14], Y=new int[14], Rows=new int[10];
    static int R,K;
    static int[] H, Parents, Uses;
    static List<int> Possible;
    static long Families,Common,Independent,Library,Eliminated,Residual;
    static int OrdBound;
    static Dictionary<uint,int> Ordinary=new Dictionary<uint,int>();
    static StreamWriter Out;

    static int Hull(uint neg,bool helpers) {
        Array.Clear(Rows,0,10); Array.Clear(Cols,0,10);
        for (int j=0;j<14;++j) {
            uint all=neg;
            if(helpers)for(int h=0;h<R;++h)all&=Miss[H[h],j];
            int x=X[j],y=Y[j];uint p=all&Raw[y],q=all&Raw[x];
            if(p!=0){Rows[x]|=1<<j;Cols[x]|=p;}
            if(q!=0){Rows[y]|=1<<j;Cols[y]|=q;}
        }
        int k=0,m=0;
        for(int i=0;i<10;++i)if(Rows[i]!=0)++k;
        for(int j=0;j<14;++j)if((Rows[X[j]]&Rows[Y[j]])!=0 && (Cols[X[j]]&Cols[Y[j]])!=0)m|=1<<j;
        return k+Cover[m];
    }

    static void ChooseParents(int i,int cost,int once,int twice,bool connected) {
        if(i==R){
            if(!connected)return;
            ++Library;
            int d=0;for(int j=0;j<R;++j)d+=Math.Max(0,2-Uses[j]);
            int cap=19-cost-d;
            if(10-Pop[twice]>cap || OrdBound>cap){++Eliminated;return;}
            ++Residual;
            Out.WriteLine(String.Join(",",Array.ConvertAll(H,h=>h.ToString()))+";"+
                          String.Join(",",Array.ConvertAll(Parents,h=>h.ToString())));
            return;
        }
        int allowed=0;
        for(int j=0;j<i;++j)if((H[j]&H[i])==H[j])allowed|=1<<j;
        for(int p=allowed;;p=(p-1)&allowed){
            int inherited=0;
            for(int j=0;j<i;++j)if((p&(1<<j))!=0)inherited|=H[j];
            int raw=H[i]&~inherited;
            int leaves=Pop[p]+Pop[raw];
            bool irredundant=leaves>=2;
            // Every direct helper operand must add a variable that the other
            // operands do not already supply.
            for(int j=0;j<i && irredundant;++j)if((p&(1<<j))!=0){
                int other=raw;
                for(int z=0;z<i;++z)if(z!=j && (p&(1<<z))!=0)other|=H[z];
                if((H[j]&~other)==0)irredundant=false;
            }
            if(irredundant){
                Parents[i]=p;
                for(int j=0;j<i;++j)if((p&(1<<j))!=0)++Uses[j];
                ChooseParents(i+1,cost+leaves-1,once|raw,twice|(once&raw),connected || p!=0);
                for(int j=0;j<i;++j)if((p&(1<<j))!=0)--Uses[j];
            }
            if(p==0)break;
        }
    }

    static void Family(int i,int start,int union,int intersect,uint positives) {
        if(i==R){
            if(union!=K)return;
            ++Families;
            if(Pop[intersect]>=2){++Common;return;}
            bool comparable=false;
            for(int a=0;a<R;++a)for(int b=0;b<a;++b)if((H[a]&H[b])==H[b])comparable=true;
            if(!comparable){++Independent;return;}
            int co;
            if(!Ordinary.TryGetValue(positives,out co)){co=Hull(positives,false);Ordinary.Add(positives,co);}
            OrdBound=Math.Max(co,Hull(N,true));
            ChooseParents(0,0,0,0,false);
            return;
        }
        for(int j=start;j<=Possible.Count-(R-i);++j){
            int a=Possible[j];H[i]=a;
            Family(i+1,j+1,union|a,intersect&a,positives&Join[a]);
        }
    }

    static void Main(string[] args){
        Raw=Array.FindAll(Array.ConvertAll(args[0].Split(','),UInt32.Parse),w=>w!=0);
        if(Raw.Length!=10)throw new Exception("expected 10 raw vertices");
        R=Int32.Parse(args[1]);if(R<3 || R>5)throw new Exception("expected three to five shared gates");
        H=new int[R];Parents=new int[R];Uses=new int[R];
        for(int s=1;s<Pop.Length;++s)Pop[s]=1+Pop[s&(s-1)];
        for(int s=0;s<1024;++s){
            for(int j=0;j<10;++j)if((s&(1<<j))!=0)Join[s]|=Raw[j];
            for(int j=0;j<14;++j)Miss[s,j]=(Join[s]&(1U<<j))==0?N:N&Join[s];
        }
        for(int j=0;j<14;++j){
            var ends=new List<int>();
            for(int i=0;i<10;++i)if((Raw[i]&(1U<<j))!=0)ends.Add(i);
            if(ends.Count!=2)throw new Exception("expected an edge");
            X[j]=ends[0];Y[j]=ends[1];
        }
        for(int s=1;s<Cover.Length;++s){
            int j=0;while((s&(1<<j))==0)++j;
            Cover[s]=1+Math.Min(Cover[s&~(int)Raw[X[j]]],Cover[s&~(int)Raw[Y[j]]]);
        }
        using(Out=new StreamWriter(args[2])){
            for(K=1;K<1024;++K)if(Pop[K]<=9-R){
                Possible=new List<int>();
                for(int s=K;s!=0;s=(s-1)&K)if(Pop[s]>=2)Possible.Add(s);
                Possible.Sort((a,b)=>Pop[a]!=Pop[b]?Pop[a]-Pop[b]:a-b);
                Family(0,0,0,1023,N);
            }
        }
        Console.WriteLine("r={0} families={1} common={2} incomparable={3} dependent={4} eliminated={5} remaining={6}",
                          R,Families,Common,Independent,Library,Eliminated,Residual);
    }
}
