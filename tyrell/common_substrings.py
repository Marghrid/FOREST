

# function to find the stem (longest   common substring) from the string array
def find_lcs(arr):
    # Determine size of the array
    n = len(arr)

    # Take first word from array as reference
    s = arr[0]
    l = len(s)

    results = set()

    for i in range(l):
        for j in range(i + 1, l + 1):

            # generating all possible substrings of our reference string arr[0] i.e s
            stem = s[i:j]
            k = 1
            for k in range(1, n):
                # Check if the generated stem is common to all words
                if stem not in arr[k]:
                    break

            # If current substring is present in all strings and its length is greater
            # than current result
            if k + 1 == n:
                if len(results) == 0:
                    results = {stem}
                elif len(next(iter(results))) < len(stem):
                    results = {stem}
                elif len(next(iter(results))) == len(stem):
                    results.add(stem)

    return list(results)

def find_all_cs(l):
    """Find longest common substring among all strings in a list"""
    if len(l) < 2:
        return ""
    else:
        common_chars = []
        substrings = []
        while True:
            for sub in substrings:
                l = [s.replace(sub, '') for s in l]
            substrings = find_lcs(l)
            if len(substrings) < 1:
                # there are no more substrings
                return common_chars
            else:
                common_chars.extend(substrings)
