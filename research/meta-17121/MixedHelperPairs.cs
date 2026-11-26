using System;
using System.Collections.Generic;
using System.IO;

// Screen a pair of independent, potentially mixed private formulas.
class MixedHelperPairs {
    const uint Target=16383U, Negative=~Target;
    static uint[] raw;
    static int[] x=new int[14],y=new int[14],cover=new int[16384],pop=new int[16384];
    static int[] rows=new int[10],ordinary=new int[1<<18];
    static uint[] cols=new uint[10];
    static List<Signal>[] ors=new List<Signal>[11], mixed=new List<Signal>[11];
    static long total,comparable,cofactor,full,pending;
    static StreamWriter writer;
    class Signal {
        public uint w;
        public int cost;
        public uint[] miss=new uint[14];
        public Signal(uint word,int g) {
            w=word;cost=g;
            for(int e=0;e<14;++e)miss[e]=(w&(1U<<e))==0?Negative:(w&Negative);
        }
    }
    static bool Normal(uint w,int g) {
        int m=(int)(w&Target);
        if(m==0 || m==(int)Target || (w&Negative)==0 || pop[m]+cover[m]-2<=g)return true;
        for(int c=0;c<=g && c<10;++c)foreach(var s in ors[c]){
            if((s.w&Negative&~w)!=0)continue;
            int lost=m&~(int)s.w;
            if(c+pop[lost]+cover[lost]<=g)return true;
        }
        return false;
    }
    static int Hull(uint neg,Signal h,Signal j,int target) {
        Array.Clear(rows,0,10);Array.Clear(cols,0,10);
        int mandatory=0;
        for(int e=0;e<14;++e){
            int a=x[e],b=y[e];uint allowed=neg;
            if(h!=null)allowed&=h.miss[e]&j.miss[e];
            uint va=raw[b]&allowed,vb=raw[a]&allowed;
            if(va!=0){
                if(rows[a]==0)++mandatory;
                rows[a]|=1<<e;cols[a]|=va;
            }
            if(vb!=0){
                if(rows[b]==0)++mandatory;
                rows[b]|=1<<e;cols[b]|=vb;
            }
            if(mandatory>target)return mandatory;
        }
        int conflict=0;
        for(int e=0;e<14;++e){
            int a=x[e],b=y[e];
            if((rows[a]&rows[b])!=0 && (cols[a]&cols[b])!=0)conflict|=1<<e;
        }
        return mandatory+cover[conflict];
    }
    static void Test(Signal h,Signal j) {
        int q=h.cost+j.cost,cap=15-q;
        ++total;
        uint eh=h.w^Target,ej=j.w^Target;
        if((eh&ej)==eh || (eh&ej)==ej){++comparable;return;}
        uint neg=h.w&j.w&Negative;
        int key=(int)(neg>>14);
        if(ordinary[key]<0)ordinary[key]=Hull(neg,null,null,100);
        if(ordinary[key]>cap){++cofactor;return;}
        if(Hull(Negative,h,j,cap)>cap){++full;return;}
        ++pending;
        writer.WriteLine(h.cost+","+h.w+","+j.cost+","+j.w);
    }
    static void Main(string[] args){
        raw=Array.FindAll(Array.ConvertAll(args[0].Split(','),UInt32.Parse),w=>w!=0);
        if(raw.Length!=10)throw new Exception("Ten raw inputs required.");
        for(int s=1;s<pop.Length;++s)pop[s]=1+pop[s&(s-1)];
        for(int e=0;e<14;++e){
            List<int> endpoints=new List<int>();
            for(int a=0;a<10;++a)if((raw[a]&(1U<<e))!=0)endpoints.Add(a);
            if(endpoints.Count!=2)throw new Exception("Expected edges.");
            x[e]=endpoints[0];y[e]=endpoints[1];
        }
        for(int m=1;m<cover.Length;++m){
            int e=0;while((m&(1<<e))==0)++e;
            cover[m]=1+Math.Min(cover[m&~(int)raw[x[e]]],cover[m&~(int)raw[y[e]]]);
        }
        for(int i=0;i<ordinary.Length;++i)ordinary[i]=-1;
        for(int i=0;i<11;++i){ors[i]=new List<Signal>();mixed[i]=new List<Signal>();}
        for(int mask=1;mask<1024;++mask){
            uint w=0;
            for(int i=0;i<10;++i)if((mask&(1<<i))!=0)w|=raw[i];
            ors[pop[mask]-1].Add(new Signal(w,pop[mask]-1));
        }
        for(int g=1;g<=10;++g){
            int count=0;
            foreach(string line in File.ReadLines(args[1].Replace("{0}",g.ToString()))){
                ++count;uint w=UInt32.Parse(line);
                if(!Normal(w,g))mixed[g].Add(new Signal(w,g));
            }
            Console.WriteLine("cost {0} words {1} residual {2}",g,count,mixed[g].Count);
        }
        using(writer=new StreamWriter(args[2])){
            for(int g=1;g<=10;++g){
                for(int i=0;i<mixed[g].Count;++i){
                    Signal h=mixed[g][i];
                    for(int d=1;d<=9 && d+g<=13;++d)foreach(var j in ors[d])Test(h,j);
                    for(int d=1;d<=g && d+g<=13;++d){
                        int n=d==g?i:mixed[d].Count;
                        for(int j=0;j<n;++j)Test(h,mixed[d][j]);
                    }
                }
                Console.WriteLine("through {0} total {1} comparable {2} cofactor {3} full {4} pending {5}",
                                  g,total,comparable,cofactor,full,pending);
                writer.Flush();
            }
        }
    }
}
