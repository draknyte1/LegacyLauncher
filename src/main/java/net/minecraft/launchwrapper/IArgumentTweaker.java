package net.minecraft.launchwrapper;

import java.util.List;

public interface IArgumentTweaker {
    void modifyArguments(List<String> arguments);
}