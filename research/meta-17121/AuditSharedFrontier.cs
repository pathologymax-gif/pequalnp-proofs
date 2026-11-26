using System;
using System.Collections.Generic;
using System.IO;

// Independent check of the supplied one-helper frontier. No insertion trie,
// rank buckets, bit counts, or generation-order deduplication are assumed.
// The candidate sets and a static branch-and-bound subset oracle are rebuilt.
class AuditSharedFrontier
{
    const uint Target = 16383;
    sealed class Group
    {
        public uint Common, Example;
        public Group Lower, Upper;
    }

    static Group Compile(uint[] sorted, int begin, int end)
    {
        Group node = new Group();
        node.Example = sorted[begin];
        if (end - begin == 1)
        {
            node.Common = node.Example;
            return node;
        }
        uint different = sorted[begin] ^ sorted[end - 1];
        uint bit = 1;
        while ((different >>= 1) != 0) bit <<= 1;
        int low = begin + 1, high = end - 1;
        while (low < high)
        {
            int mid = low + (high - low) / 2;
            if ((sorted[mid] & bit) == 0) low = mid + 1;
            else high = mid;
        }
        node.Lower = Compile(sorted, begin, low);
        node.Upper = Compile(sorted, low, end);
        node.Common = node.Lower.Common & node.Upper.Common;
        return node;
    }

    // Is some member disjoint from "forbidden"? The bitwise intersection of
    // each group is a necessary condition, its representative is sufficient.
    static bool Covers(Group node, uint forbidden)
    {
        if ((node.Common & forbidden) != 0) return false;
        if ((node.Example & forbidden) == 0) return true;
        return node.Lower != null &&
               (Covers(node.Lower, forbidden) || Covers(node.Upper, forbidden));
    }

    static void Check(string input, string directory, int row)
    {
        uint[] seed = Array.ConvertAll(input.Split(','), UInt32.Parse);
        var levels = new List<uint[]>();
        levels.Add(Array.ConvertAll(seed, w => w ^ Target));
        var throughCost = new HashSet<uint>(levels[0]);
        long total = 0;
        for (int cost = 1; cost <= 11; ++cost)
        {
            string file = Path.Combine(directory, cost + ".txt");
            var declared = Array.ConvertAll(File.ReadAllLines(file), s => UInt32.Parse(s) ^ Target);
            var candidates = new HashSet<uint>();
            for (int a = 0; a < cost; ++a)
            {
                int b = cost - 1 - a;
                if (a > b) break;
                foreach (uint x in levels[a])
                foreach (uint y in levels[b])
                {
                    uint uni = x | y, inter = x & y;
                    candidates.Add((uni & Target) | (inter & ~Target));
                    candidates.Add((inter & Target) | (uni & ~Target));
                }
            }
            foreach (uint mask in declared)
                if (!candidates.Contains(mask) || !throughCost.Add(mask))
                    throw new Exception("Unattained or repeated retained mask");
            var sorted = new uint[throughCost.Count];
            throughCost.CopyTo(sorted);
            Array.Sort(sorted);
            Group root = Compile(sorted, 0, sorted.Length);
            foreach (uint mask in candidates)
                if (!throughCost.Contains(mask) && !Covers(root, ~mask))
                    throw new Exception("Undominated missing candidate: " + mask);
            levels.Add(declared);
            total += candidates.Count;
            Console.WriteLine("Row {0} cost {1}: {2} candidate values, {3} retained, all covered",
                              row, cost, candidates.Count, declared.Length);
        }
        Console.WriteLine("Row {0}: {1} distinct candidate values over 11 exact strata", row, total);
    }

    static void Main(string[] args)
    {
        Check(args[0], args[1], Int32.Parse(args[2]));
    }
}
