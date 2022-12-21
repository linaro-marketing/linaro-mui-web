import React, { createContext, useContext } from "react";
import {
  ThemeProvider as MuiThemeProvider,
  useMediaQuery,
} from "@mui/material";
import { useLocalStorage } from "lib/hooks";
import { ThemeOptions } from "@mui/material";
const DARK_SCHEME_QUERY = "(prefers-color-scheme: dark)";

const ThemeContext = createContext({});
const useThemeContext = () => useContext(ThemeContext);

const ThemeProvider = ({
  lightTheme,
  darkTheme,
  children,
}: {
  lightTheme: ThemeOptions;
  darkTheme: ThemeOptions;
  children: React.ReactNode;
}) => {
  const isDarkOS = useMediaQuery(DARK_SCHEME_QUERY);

  const [themeMode, setThemeMode] = useLocalStorage(
    "themeMode",
    isDarkOS ? "light" : "dark"
  );
  function setClassOnDocumentBody(mode) {
    let classNameDark = "dark";
    let classNameLight = "light";
    document.body.classList.add(
      mode === "dark" ? classNameDark : classNameLight
    );
    document.body.classList.remove(
      mode === "dark" ? classNameLight : classNameDark
    );
  }
  const toggleTheme = () => {
    console.log("Theme is toggled: ", themeMode);
    if (themeMode === "light") {
      setClassOnDocumentBody("dark");
      setThemeMode("dark");
    } else {
      setClassOnDocumentBody("light");
      setThemeMode("light");
    }
  };

  return (
    <ThemeContext.Provider value={{ themeMode, toggleTheme }}>
      <MuiThemeProvider theme={themeMode === "light" ? lightTheme : darkTheme}>
        {children}
      </MuiThemeProvider>
    </ThemeContext.Provider>
  );
};

export { useThemeContext, ThemeProvider };
