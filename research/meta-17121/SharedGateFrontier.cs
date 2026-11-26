using System;
using System.Collections.Generic;
using System.IO;

// Enumerate the undominated truth masks at each minimum formula cost.
// The target's 14 positive bits are the low bits of the unsigned word.
class SharedGateFrontier {
    const uint Target = 16383U;
    static readonly List<int[]> Trie = new List<int[]> { new int[2] };

    static void Insert(uint key) {
        int node = 0;
        for (int bit = 0; bit < 32; ++bit) {
            int side = (int)((key >> bit) & 1);
            if (Trie[node][side] == 0) {
                Trie[node][side] = Trie.Count;
                Trie.Add(new int[2]);
            }
            node = Trie[node][side];
        }
    }

    static bool HasSubset(uint key, int node, int bit) {
        if (bit == 32) return true;
        int[] edges = Trie[node];
        return (edges[0] != 0 && HasSubset(key, edges[0], bit + 1))
            || (((key >> bit) & 1) != 0 && edges[1] != 0 && HasSubset(key, edges[1], bit + 1));
    }

    static int PopCount(uint x) {
        x -= (x >> 1) & 0x55555555U;
        x = (x & 0x33333333U) + ((x >> 2) & 0x33333333U);
        return (int)((((x + (x >> 4)) & 0x0f0f0f0fU) * 0x01010101U) >> 24);
    }

    public static void Main(string[] args) {
        var seeds = Array.ConvertAll(args[0].Split(','), UInt32.Parse);
        var levels = new List<List<uint>> { new List<uint>(seeds) };
        foreach (uint word in seeds) Insert(word ^ Target);

        for (int cost = 1; cost <= 11; ++cost) {
            var masks = new HashSet<uint>();
            for (int left = 0; left <= (cost - 1) / 2; ++left) {
                int right = cost - 1 - left;
                foreach (uint x in levels[left]) foreach (uint y in levels[right]) {
                    masks.Add((x & y) ^ Target);
                    masks.Add((x | y) ^ Target);
                }
            }
            var buckets = new List<uint>[33];
            for (int i = 0; i < buckets.Length; ++i) buckets[i] = new List<uint>();
            foreach (uint mask in masks) buckets[PopCount(mask)].Add(mask);
            var keep = new List<uint>();
            foreach (var bucket in buckets) foreach (uint mask in bucket) {
                if (mask == 0) throw new InvalidOperationException("Found a target formula of size at most 11.");
                if (!HasSubset(mask, 0, 0)) {
                    Insert(mask);
                    keep.Add(mask ^ Target);
                }
            }
            File.WriteAllLines(Path.Combine(args[1], cost + ".txt"),
                               keep.ConvertAll(w => w.ToString()).ToArray());
            levels.Add(keep);
        }
    }
}
