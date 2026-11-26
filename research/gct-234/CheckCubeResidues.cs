// Independent finite-field tests for the three-cube positive-root multiplicity question.
// Enumerates every prime from 11 through 101 unless two inclusive bounds are supplied.
// On Windows with .NET Framework, from this file's directory in PowerShell:
//   & "$env:WINDIR\Microsoft.NET\Framework64\v4.0.30319\csc.exe" /nologo /optimize+ /out:CheckCubeResidues.exe CheckCubeResidues.cs
//   .\CheckCubeResidues.exe
// Or with .NET 10+: dotnet run --file CheckCubeResidues.cs
// No packages or auxiliary data files are needed.

using System;
using System.Collections.Generic;

public static class CheckCubeResidues
{
    private struct Four
    {
        public int A, B, C, D;
        public Four(int a, int b, int c, int d) { A = a; B = b; C = c; D = d; }
        public int At(int j) { return j == 0 ? A : j == 1 ? B : j == 2 ? C : D; }
    }

    private sealed class Block
    {
        public Four Nodes;
        public ulong LowMask, HighMask;
        public int BaseCollisions;
        public Four ContributionAtBase;

        public Block(int a, int b, int p)
        {
            Nodes = new Four(3*a % p, (2*a+b) % p, (a+2*b) % p, 3*b % p);
            for (int i = 0; i < 4; i++)
            {
                int x = Nodes.At(i);
                if (x < 64) LowMask |= 1UL << x;
                else HighMask |= 1UL << (x-64);
                if (x <= 3) BaseCollisions++;
            }
        }
    }

    private static int Mod(int x, int p) { int r = x % p; return r < 0 ? r+p : r; }

    private static Four Multiply(Four a, Four b, int p)
    {
        return new Four(a.A*b.A % p, a.B*b.B % p, a.C*b.C % p, a.D*b.D % p);
    }

    private static int NodalValue(Four roots, int x, int p)
    {
        return Mod(((x-roots.A)*(x-roots.B) % p) * ((x-roots.C)*(x-roots.D) % p), p);
    }

    private static Four NodalValues(Four roots, Four nodes, int p)
    {
        return new Four(NodalValue(roots, nodes.A, p), NodalValue(roots, nodes.B, p),
                        NodalValue(roots, nodes.C, p), NodalValue(roots, nodes.D, p));
    }

    private sealed class RepeatedCubics
    {
        private readonly int p;
        private readonly int[] inverse;
        private readonly HashSet<int> catalog = new HashSet<int>();

        public RepeatedCubics(int prime)
        {
            p = prime;
            inverse = new int[p];
            inverse[1] = 1;
            for (int i = 2; i < p; i++) inverse[i] = p - (p/i)*inverse[p%i] % p;
            catalog.Add(0);

            // A nonzero repeated-root binary cubic over F_p factors as l^2 m there:
            // a non-rational double root would bring its conjugate and require degree >=4.
            // The representative p denotes the projective point at infinity.
            for (int doubleRoot = 0; doubleRoot <= p; doubleRoot++)
            for (int otherRoot = 0; otherRoot <= p; otherRoot++)
            {
                int u = doubleRoot == p ? 0 : 1;
                int v = doubleRoot == p ? 1 : -doubleRoot;
                int w = otherRoot == p ? 0 : 1;
                int z = otherRoot == p ? 1 : -otherRoot;
                // (uT+vS)^2 (wT+zS), in ascending powers of T.
                catalog.Add(Key(Mod(v*v*z, p), Mod(v*v*w+2*u*v*z, p),
                                Mod(2*u*v*w+u*u*z, p), Mod(u*u*w, p)));
            }
            if (catalog.Count != (p+1)*(p+1)+1) throw new Exception("Invalid cubic catalog");
        }

        private int Key(int a, int b, int c, int d)
        {
            int first = a != 0 ? a : b != 0 ? b : c != 0 ? c : d;
            if (first == 0) return 0;
            int scale = inverse[first];
            return (((a*scale % p)*p + b*scale % p)*p + c*scale % p)*p + d*scale % p;
        }

        public bool Contains(Four nodes)
        {
            return catalog.Contains(Key(nodes.A, 3*nodes.B % p, 3*nodes.C % p, nodes.D));
        }
    }

    private static bool TooManyCollisions(Block a, Block b)
    {
        int existing = a.BaseCollisions+b.BaseCollisions;
        if (existing > 1) return true;
        ulong low = a.LowMask & b.LowMask, high = a.HighMask & b.HighMask;
        if ((low | high) == 0) return false;
        if (existing != 0 || (low != 0 && high != 0)) return true;
        ulong bits = low | high;
        return (bits & (bits-1)) != 0;
    }

    private static int GeometricValue(Four nodes, Four factors, int j, int u, int v, int p)
    {
        int l0 = (u*nodes.At(j)+v) % p;
        int l1 = (u*nodes.At(j+1)+v) % p;
        int l2 = (u*nodes.At(j+2)+v) % p;
        int q0 = factors.At(j), q1 = factors.At(j+1), q2 = factors.At(j+2);
        return Mod(l1*l1*q0*q2 - l0*l2*q1*q1, p);
    }

    // A null list represents the zero polynomial, vanishing on the entire projective line.
    private static List<int> Roots(Four nodes, Four factors, int j, int p, int nonsquare)
    {
        int a = GeometricValue(nodes, factors, j, 1, 0, p);
        int c = GeometricValue(nodes, factors, j, 0, 1, p);
        int b = Mod(GeometricValue(nodes, factors, j, 1, 1, p)-a-c, p);
        if (a == 0 && b == 0 && c == 0) return null;
        List<int> result = new List<int>(2);
        if (a == 0) result.Add(p*p); // infinity
        // x+y sqrt(nonsquare), all points of F_{p^2}. Every quadratic splits here.
        for (int y = 0; y < p; y++)
        for (int x = 0; x < p; x++)
        {
            if (((2*a*x+b)*y) % p != 0) continue;
            if ((a*(x*x+nonsquare*y*y)+b*x+c) % p == 0) result.Add(x+p*y);
        }
        if (result.Count == 0 || result.Count > 2) throw new Exception("Invalid quadratic roots");
        return result;
    }

    private static bool PairwiseRoots(Four[] nodes, Four[] factors, int p, int nonsquare)
    {
        List<List<int>> prior = new List<List<int>>();
        for (int i = 0; i < 3; i++)
        for (int j = 0; j < 2; j++)
        {
            List<int> roots = Roots(nodes[i], factors[i], j, p, nonsquare);
            if (roots == null) continue;
            foreach (List<int> previous in prior)
            {
                bool shared = false;
                foreach (int x in roots) if (previous.Contains(x)) shared = true;
                if (!shared) return false;
            }
            prior.Add(roots);
        }
        return true;
    }

    private static bool IsPrime(int p)
    {
        for (int i = 2; i*i <= p; i++) if (p % i == 0) return false;
        return p >= 2;
    }

    private static long RunPrime(int p)
    {
        Four basis = new Four(0, 1, 2, 3);
        List<Block> others = new List<Block>();
        for (int a = 0; a < p; a++)
        for (int b = a+1; b < p; b++)
        {
            Block block = new Block(a, b, p);
            if (block.BaseCollisions > 1) continue;
            block.ContributionAtBase = NodalValues(block.Nodes, basis, p);
            others.Add(block);
        }
        RepeatedCubics catalog = new RepeatedCubics(p);
        bool[] isSquare = new bool[p];
        for (int x = 0; x < p; x++) isSquare[x*x % p] = true;
        int nonsquare = 2;
        while (isSquare[nonsquare]) nonsquare++;

        long eligible = 0, first = 0, allCubics = 0, allPairs = 0;
        for (int i = 0; i < others.Count; i++)
        {
            Block a = others[i];
            Four atA = NodalValues(basis, a.Nodes, p);
            for (int j = i+1; j < others.Count; j++)
            {
                Block b = others[j];
                if (TooManyCollisions(a, b)) continue;
                eligible++;
                Four qa = Multiply(a.ContributionAtBase, b.ContributionAtBase, p);
                if (!catalog.Contains(qa)) continue;
                first++;
                Four qb = Multiply(atA, NodalValues(b.Nodes, a.Nodes, p), p);
                if (!catalog.Contains(qb)) continue;
                Four qc = Multiply(NodalValues(basis, b.Nodes, p), NodalValues(a.Nodes, b.Nodes, p), p);
                if (!catalog.Contains(qc)) continue;
                allCubics++;
                if (!PairwiseRoots(new Four[] {basis, a.Nodes, b.Nodes}, new Four[] {qa,qb,qc}, p, nonsquare)) continue;
                allPairs++;
                Console.WriteLine("survivor p={0}, other endpoints {1},{2} and {3},{4} (cubed exponents)",
                                  p, a.Nodes.A, a.Nodes.D, b.Nodes.A, b.Nodes.D);
            }
        }
        Console.WriteLine("{0},{1},{2},{3},{4}", p, eligible, first, allCubics, allPairs);
        return allPairs;
    }

    public static int Main(string[] args)
    {
        int low = args.Length == 0 ? 11 : int.Parse(args[0]);
        int high = args.Length == 0 ? 101 : args.Length == 1 ? low : int.Parse(args[1]);
        if (low < 11 || high > 101 || low > high) throw new ArgumentOutOfRangeException();
        Console.WriteLine("prime,eligible,first_repeated_cubic,three_repeated_cubics,all_pairwise_resultants_zero");
        long survivors = 0;
        for (int p = low; p <= high; p++) if (IsPrime(p)) survivors += RunPrime(p);
        return survivors == 0 ? 0 : 1;
    }
}
