using System;
using System.Collections.Generic;
using System.IO;

// Screen independent OR trees, with at least one nonbinary support.
class ManyOrTrees
{
    const uint Target = 16383;
    const uint Negative = ~Target;
    static readonly int[] Pop = new int[1 << 14];
    static uint[] Raw;
    static uint[] Joined = new uint[1024];
    static uint[,] Unavailable = new uint[1024,14];
    static int[] Left = new int[14], Right = new int[14], Cover = new int[1 << 14];
    static uint[] Cols = new uint[10];
    static int[] Rows = new int[10];
    static int R, MaxExtra;
    static List<int> Supports = new List<int>();
    static int[] Choice;
    static long[] Scanned, Degree, Cofactor, Full, Pending;
    static StreamWriter Writer;
    static Dictionary<uint,int> Ordinary = new Dictionary<uint,int>();

    static int Hull(uint neg, bool allowHelpers)
    {
        Array.Clear(Rows,0,10);
        Array.Clear(Cols,0,10);
        for (int e=0; e<14; ++e)
        {
            uint avail=neg;
            if (allowHelpers)
                for (int j=0; j<R; ++j) avail &= Unavailable[Choice[j],e];
            int a=Left[e], b=Right[e], bit=1<<e;
            uint ca=avail&Raw[b], cb=avail&Raw[a];
            if (ca!=0) { Rows[a]|=bit; Cols[a]|=ca; }
            if (cb!=0) { Rows[b]|=bit; Cols[b]|=cb; }
        }
        int mandatory=0, conflict=0;
        for (int i=0; i<10; ++i) if (Rows[i]!=0) ++mandatory;
        for (int e=0; e<14; ++e)
            if ((Rows[Left[e]]&Rows[Right[e]])!=0 && (Cols[Left[e]]&Cols[Right[e]])!=0)
                conflict|=1<<e;
        return mandatory+Cover[conflict];
    }

    static void Visit(int start, int depth, int extra, int used, int repeated, uint neg)
    {
        if (depth == R)
        {
            if (extra==0) return;
            ++Scanned[extra];
            int budget = 19-3*R-extra;
            if (10-Pop[repeated]>budget) { ++Degree[extra]; return; }
            int ordinary;
            if (!Ordinary.TryGetValue(neg,out ordinary))
            {
                ordinary=Hull(neg,false);
                Ordinary.Add(neg,ordinary);
            }
            if (ordinary>budget) { ++Cofactor[extra]; return; }
            if (Hull(Negative,true)>budget) { ++Full[extra]; return; }
            ++Pending[extra];
            Writer.WriteLine(String.Join(",",Array.ConvertAll(Choice,s=>s.ToString())));
            return;
        }
        for (int i=start; i<Supports.Count; ++i)
        {
            int s=Supports[i];
            if (extra+(R-depth)*(Pop[s]-2)>MaxExtra) break;
            Choice[depth]=s;
            Visit(i+1,depth+1,extra+Pop[s]-2,used|s,repeated|(used&s),neg&Joined[s]);
        }
    }

    static void Main(string[] args)
    {
        Raw=Array.FindAll(Array.ConvertAll(args[0].Split(','),UInt32.Parse),w=>w!=0);
        if (Raw.Length!=10) throw new Exception("expected ten variables");
        R=Int32.Parse(args[1]);
        MaxExtra=R==3 ? 6 : R==4 ? 2 : 0;
        if (MaxExtra==0) throw new Exception("use three or four helpers");
        Choice=new int[R];
        Scanned=new long[MaxExtra+1]; Degree=new long[MaxExtra+1];
        Cofactor=new long[MaxExtra+1]; Full=new long[MaxExtra+1]; Pending=new long[MaxExtra+1];
        for (int s=1; s<Pop.Length; ++s) Pop[s]=1+Pop[s&(s-1)];
        for (int s=1; s<1024; ++s)
        {
            for (int j=0; j<10; ++j) if ((s&(1<<j))!=0) Joined[s]|=Raw[j];
            if (Pop[s]>=2 && Pop[s]<=2+MaxExtra) Supports.Add(s);
            for (int e=0; e<14; ++e)
                Unavailable[s,e]=(Joined[s]&(1U<<e))==0 ? Negative : Joined[s]&Negative;
        }
        Supports.Sort((a,b)=>Pop[a]!=Pop[b] ? Pop[a]-Pop[b] : a-b);
        for (int e=0; e<14; ++e)
        {
            var ends=new List<int>();
            for (int i=0;i<10;++i) if ((Raw[i]&(1U<<e))!=0) ends.Add(i);
            if (ends.Count!=2) throw new Exception("edge must have two endpoints");
            Left[e]=ends[0]; Right[e]=ends[1];
        }
        for (int s=1;s<Cover.Length;++s)
        {
            int e=0; while ((s&(1<<e))==0) ++e;
            Cover[s]=1+Math.Min(Cover[s & ~(int)Raw[Left[e]]],Cover[s & ~(int)Raw[Right[e]]]);
        }
        using (Writer=new StreamWriter(args[2])) Visit(0,0,0,0,0,Negative);
        for (int t=1;t<=MaxExtra;++t)
            Console.WriteLine("r={0} t={1} families={2} degree={3} all-one hull={4} full hull={5} remaining={6}",
                              R,t,Scanned[t],Degree[t],Cofactor[t],Full[t],Pending[t]);
    }
}
