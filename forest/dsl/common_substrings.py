def find_lcs(strings):
    """ Find longest common substring of all strings in list """

    num_strings = len(strings)

    # Take first word from array as reference
    len_0 = len(strings[0])
    results = set()

    for i in range(len_0):
        for j in range(i + 1, len_0 + 1):

            # generating all possible substrings of our reference strings[0] i.e s
            stem = strings[0][i:j]
            stem_in_all_strings = True
            for k in range(1, num_strings):
                # Check if the generated stem is common to all words
                if stem not in strings[k]:
                    stem_in_all_strings = False
                    break

            # If current substring is present in all strings and its length is greater
            # than current result
            if stem_in_all_strings:
                if len(results) == 0:
                    results = {stem}
                elif len(next(iter(results))) < len(stem):
                    results = {stem}
                elif len(next(iter(results))) == len(stem):
                    results.add(stem)

    return list(results)


def find_all_cs(strings):
    """ Find all common substrings among all strings in a list """
    if len(strings) < 2:
        return ""
    else:
        common_chars = []
        substrings = []
        while True:
            for sub in substrings:
                strings = [s.replace(sub, '') for s in strings]
            substrings = find_lcs(strings)
            if len(substrings) < 1:
                # there are no more substrings
                return common_chars
            else:
                common_chars.extend(substrings)
