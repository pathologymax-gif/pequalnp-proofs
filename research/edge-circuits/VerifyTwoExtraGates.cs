// Independent exhaustive check of graph edge functions with at most n+1 gates.
// Inputs are the n nonisolated vertices of a labeled simple graph, 2 <= n <= 6.
// Every binary AND, binary OR, and unary NOT costs one gate. Fanout is free.
// The output accepts exactly the vertex subsets containing an edge.
//
// Run with .NET 10 or newer:
//   dotnet run --file VerifyTwoExtraGates.cs
//   dotnet run --file VerifyTwoExtraGates.cs -- --classes
// Or in Windows PowerShell from the directory containing this file:
//   Add-Type -Path .\VerifyTwoExtraGates.cs
//   [VerifyTwoExtraGates]::Main([string[]]@('--classes'))
// No third-party packages or input files are needed.
//
// Gates are added in topological order, sorted by nondecreasing depth. A gate
// can read any input or earlier gate. Give fresh inputs consecutive labels in
// order of first use; restore every permutation when counting labeled graphs.
// This construction is independent of the plane-tree/backreference enumerator.
//
// For a circuit on n essential inputs, its connected output cone with b binary
// and u unary gates has 2b+u wires and n+b+u vertices, so b >= n-1. At budget
// n+1 at most two gates can be NOT. Remove dead gates. A constant signal can
// be propagated away, and a signal equal on every assignment to an existing
// wire can be replaced by that wire. These simplifications suffice when finding
// minimum size; in particular it is safe to skip binary gates reading one wire
// twice. All graph tests use the full truth table, including the nonmonotone
// intermediate signals that can arise in circuits with NOT.

using System;
using System.Collections.Generic;

public sealed class VerifyTwoExtraGates
{
    private readonly int n;
    private readonly int budget;
    private readonly ulong allAssignments;
    private readonly ulong[] wireTables;
    private readonly int[] wireDepths;
    private readonly int[,] edgeIndex;
    private readonly Dictionary<ulong, int> graphForTable = new Dictionary<ulong, int>();
    private readonly Dictionary<int, int> anyMinimum = new Dictionary<int, int>();
    private readonly Dictionary<int, int> monotoneMinimum = new Dictionary<int, int>();

    private VerifyTwoExtraGates(int vertices)
    {
        n = vertices;
        budget = n + 1;
        wireTables = new ulong[n + budget];
        wireDepths = new int[n + budget];
        edgeIndex = new int[n, n];
        int assignmentCount = 1 << n;
        allAssignments = n == 6 ? ulong.MaxValue : (1UL << assignmentCount) - 1;
        for (int v = 0; v < n; v++)
        {
            for (int assignment = 0; assignment < assignmentCount; assignment++)
            {
                if ((assignment & (1 << v)) != 0)
                    wireTables[v] |= 1UL << assignment;
            }
        }
        IndexGraphs();
    }

    private void IndexGraphs()
    {
        var endpoints = new List<int>();
        var edgeTables = new List<ulong>();
        for (int a = 0; a < n; a++)
        {
            for (int b = a + 1; b < n; b++)
            {
                edgeIndex[a, b] = edgeIndex[b, a] = endpoints.Count;
                endpoints.Add((1 << a) | (1 << b));
                edgeTables.Add(wireTables[a] & wireTables[b]);
            }
        }
        for (int graph = 1; graph < (1 << endpoints.Count); graph++)
        {
            int support = 0;
            ulong table = 0;
            for (int i = 0; i < endpoints.Count; i++)
            {
                if ((graph & (1 << i)) == 0) continue;
                support |= endpoints[i];
                table |= edgeTables[i];
            }
            if (support == (1 << n) - 1) graphForTable.Add(table, graph);
        }
    }

    private static int CountBits(int x)
    {
        int count = 0;
        while (x != 0)
        {
            x &= x - 1;
            count++;
        }
        return count;
    }

    private static void Record(Dictionary<int, int> minimum, int graph, int size)
    {
        int oldSize;
        if (!minimum.TryGetValue(graph, out oldSize) || size < oldSize)
            minimum[graph] = size;
    }

    // Open roots are earlier gate outputs no later gate has consumed yet.
    // Inputs whose first occurrence is a later gate are counted separately.
    private int Use(int roots, int wire)
    {
        return wire < n ? roots : roots & ~(1 << (wire - n));
    }

    private void TryGate(int g, int inputs, int roots, int nots, int depth, ulong table)
    {
        if (g > 0 && depth < wireDepths[n + g - 1]) return;

        // After this gate, its own output, every untouched root, and every
        // unseen essential input must ultimately join the one output cone.
        // A future binary gate can reduce their total outstanding count by at
        // most one. A unary gate cannot reduce it at all.
        int outstanding = 1 + CountBits(roots) + n - inputs;
        if (outstanding - 1 > budget - (g + 1)) return;
        if (table == 0 || table == allAssignments) return;
        for (int v = 0; v < inputs; v++)
            if (wireTables[v] == table) return;
        for (int k = 0; k < g; k++)
            if (wireTables[n + k] == table) return;

        if (inputs == n && roots == 0)
        {
            int graph;
            if (graphForTable.TryGetValue(table, out graph))
            {
                Record(anyMinimum, graph, g + 1);
                if (nots == 0) Record(monotoneMinimum, graph, g + 1);
            }
        }
        if (g + 1 == budget) return;
        wireTables[n + g] = table;
        wireDepths[n + g] = depth;
        Extend(g + 1, inputs, roots | (1 << g), nots);
    }

    private void Unary(int g, int inputs, int roots, int nots, int a)
    {
        if (nots >= 2) return;
        TryGate(g, inputs, Use(roots, a), nots + 1, wireDepths[a] + 1,
                allAssignments ^ wireTables[a]);
    }

    private void Binary(int g, int inputs, int roots, int nots, int a, int b)
    {
        int nextRoots = Use(Use(roots, a), b);
        int depth = 1 + Math.Max(wireDepths[a], wireDepths[b]);
        TryGate(g, inputs, nextRoots, nots, depth, wireTables[a] & wireTables[b]);
        TryGate(g, inputs, nextRoots, nots, depth, wireTables[a] | wireTables[b]);
    }

    private int ExistingWire(int position, int inputs)
    {
        return position < inputs ? position : n + position - inputs;
    }

    private void Extend(int g, int inputs, int roots, int nots)
    {
        int existing = inputs + g;
        for (int i = 0; i < existing; i++)
        {
            int a = ExistingWire(i, inputs);
            Unary(g, inputs, roots, nots, a);
            for (int j = i + 1; j < existing; j++)
                Binary(g, inputs, roots, nots, a, ExistingWire(j, inputs));
            if (inputs < n)
                Binary(g, inputs + 1, roots, nots, a, inputs);
        }
        if (inputs < n)
            Unary(g, inputs + 1, roots, nots, inputs);
        if (inputs + 1 < n)
            Binary(g, inputs + 2, roots, nots, inputs, inputs + 1);
    }

    private void PermuteGraph(int graph, int[] perm, int i, int used, HashSet<int> orbit)
    {
        if (i == n)
        {
            int renamed = 0;
            for (int a = 0; a < n; a++)
            {
                for (int b = a + 1; b < n; b++)
                {
                    if ((graph & (1 << edgeIndex[a, b])) != 0)
                        renamed |= 1 << edgeIndex[perm[a], perm[b]];
                }
            }
            orbit.Add(renamed);
            return;
        }
        for (int v = 0; v < n; v++)
        {
            if ((used & (1 << v)) != 0) continue;
            perm[i] = v;
            PermuteGraph(graph, perm, i + 1, used | (1 << v), orbit);
        }
    }

    private Dictionary<int, int> ExpandOrbits(Dictionary<int, int> discovered,
                                              List<int> topRepresentatives)
    {
        var labeled = new Dictionary<int, int>();
        for (int cost = n - 1; cost <= budget; cost++)
        {
            foreach (var item in discovered)
            {
                if (item.Value != cost || labeled.ContainsKey(item.Key)) continue;
                var orbit = new HashSet<int>();
                PermuteGraph(item.Key, new int[n], 0, 0, orbit);
                int least = item.Key;
                foreach (int graph in orbit)
                {
                    labeled.Add(graph, cost);
                    least = Math.Min(least, graph);
                }
                if (cost == budget) topRepresentatives.Add(least);
            }
        }
        topRepresentatives.Sort();
        return labeled;
    }

    private void Report(bool showClasses)
    {
        Extend(0, 0, 0, 0);
        var reps = new List<int>();
        var labeled = ExpandOrbits(anyMinimum, reps);
        var monotone = ExpandOrbits(monotoneMinimum, new List<int>());
        int[] counts = new int[3];
        int helped = 0;
        foreach (var item in labeled)
        {
            counts[item.Value - (n - 1)]++;
            int cost;
            if (!monotone.TryGetValue(item.Key, out cost) || cost > item.Value) helped++;
        }
        Console.WriteLine("{0,1} {1,9} {2,7} {3,7} {4,7} {5,10} {6,10}",
            n, graphForTable.Count, counts[0], counts[1], counts[2], reps.Count, helped);
        if (showClasses)
            Console.WriteLine("  n+1 representative edge masks: [{0}]", string.Join(", ", reps));
    }

    public static void Main(string[] args)
    {
        if (args.Length > 1 || (args.Length == 1 && args[0] != "--classes"))
            throw new ArgumentException("The only option is --classes.");
        Console.WriteLine("n  eligible     n-1       n     n+1      types NOT helped");
        for (int vertices = 2; vertices <= 6; vertices++)
            new VerifyTwoExtraGates(vertices).Report(args.Length == 1);
    }
}
